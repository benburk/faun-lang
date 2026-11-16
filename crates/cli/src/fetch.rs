//! Fetching URL dependencies into the user's cache.
//!
//! A bundle is downloaded once, checked against the hash its URL names, and
//! unpacked into a staging directory that is moved into place with a
//! rename, so a directory named by a hash always holds a whole package.
//! Everything a build reads is then on disk; the compiler itself never
//! reaches the network.

use std::fs;
use std::io::{self, Read};
use std::path::{Component, Path, PathBuf};
use std::time::{Duration, SystemTime};

use faun_frontend::diagnostic::Diagnostic;
use faun_frontend::packages::{self, Fetch, PackageUrl, Packages};

/// The most a bundle may unpack to.
const BUNDLE_LIMIT: u64 = 10 << 20;

/// The most every bundle one command fetches may unpack to together.
const TOTAL_LIMIT: u64 = 100 << 20;

/// How many redirects a download follows.
const REDIRECTS: usize = 3;

/// How old a staging directory is before it is taken for one a killed
/// process left.
const STALE: Duration = Duration::from_hours(24);

/// Fetches bundles into the cache at `root`, and counts what it unpacks.
pub(crate) struct Fetcher {
    root: PathBuf,
    agent: ureq::Agent,
    unpacked: u64,
    /// How many bundles it downloaded, rather than found cached.
    pub(crate) downloaded: usize,
}

impl Fetcher {
    /// A fetcher using the user's cache: `$FAUN_CACHE`, or `faun` under
    /// `$XDG_CACHE_HOME`, or under `~/.cache` where that is unset.
    pub(crate) fn new() -> Result<Self, Diagnostic> {
        let root = std::env::var_os("FAUN_CACHE")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("XDG_CACHE_HOME")
                    .filter(|value| !value.is_empty())
                    .map(|cache| PathBuf::from(cache).join("faun"))
            })
            .or_else(|| {
                std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache/faun"))
            })
            .ok_or_else(|| {
                Diagnostic::new(
                    "no cache to fetch into: neither `XDG_CACHE_HOME` nor `HOME` is set",
                )
            })?;
        let agent = ureq::Agent::config_builder()
            .max_redirects(0)
            .http_status_as_error(false)
            .build()
            .into();
        Ok(Self {
            root,
            agent,
            unpacked: 0,
            downloaded: 0,
        })
    }

    /// Fetch what the package at `source` reaches, and choose its versions.
    pub(crate) fn resolve(&mut self, source: &Path) -> Result<Packages, Diagnostic> {
        packages::resolve(source, self)
    }

    /// The bytes at `url`, following at most [`REDIRECTS`] redirects, each to
    /// a place a dependency's URL may name.
    fn download(&self, url: &str) -> Result<Vec<u8>, Diagnostic> {
        let mut at = url.to_owned();
        for _ in 0..=REDIRECTS {
            let failed = |error: &dyn std::fmt::Display| {
                Diagnostic::new(format!("cannot download `{at}`: {error}"))
            };
            let response = self.agent.get(&at).call().map_err(|error| failed(&error))?;
            let status = response.status();
            if status.is_redirection() {
                let location = response
                    .headers()
                    .get("location")
                    .and_then(|value| value.to_str().ok())
                    .ok_or_else(|| failed(&"a redirect with no location"))?;
                let next = joined(&at, location);
                if !allowed(&next) {
                    return Err(failed(&format!(
                        "it redirects to `{next}`, which is not `https`"
                    )));
                }
                at = next;
                continue;
            }
            if !status.is_success() {
                return Err(failed(&format!("the server answers {status}")));
            }
            let mut bytes = Vec::new();
            response
                .into_body()
                .into_reader()
                .take(BUNDLE_LIMIT + 1)
                .read_to_end(&mut bytes)
                .map_err(|error| failed(&error))?;
            if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > BUNDLE_LIMIT {
                return Err(failed(&"it is larger than a bundle may be, 10 megabytes"));
            }
            return Ok(bytes);
        }
        Err(Diagnostic::new(format!(
            "cannot download `{url}`: it redirects more than {REDIRECTS} times"
        )))
    }

    /// Unpack `bundle` into `into`, by way of a staging directory.
    fn unpack(&mut self, bundle: &[u8], into: &Path, url: &str) -> Result<(), Diagnostic> {
        let staging_root = self.root.join("staging");
        clear_stale(&staging_root);
        let nanos = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_or(0, |since| since.as_nanos());
        let staging = staging_root.join(format!("{}-{nanos}", std::process::id()));
        let refused = |message: String| Diagnostic::new(format!("the bundle `{url}` {message}"));
        fs::create_dir_all(&staging)
            .map_err(|error| refused(format!("cannot be unpacked: {error}")))?;
        let total = match extract(bundle, &staging) {
            Ok(total) => total,
            Err(message) => {
                let _ = fs::remove_dir_all(&staging);
                return Err(refused(message));
            }
        };
        self.unpacked += total;
        if self.unpacked > TOTAL_LIMIT {
            let _ = fs::remove_dir_all(&staging);
            return Err(Diagnostic::new(
                "the packages fetched unpack to more than 100 megabytes together",
            ));
        }
        read_only(&staging);
        if let Some(parent) = into.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| refused(format!("cannot be unpacked: {error}")))?;
        }
        if fs::rename(&staging, into).is_err() {
            // Another process put the same package in place first.
            let _ = fs::remove_dir_all(&staging);
            if !into.join("main.fn").is_file() {
                return Err(refused("cannot be moved into the cache".to_owned()));
            }
        }
        Ok(())
    }
}

/// Unpack `bundle` into `staging`: only files and directories, each inside
/// it, at most [`BUNDLE_LIMIT`] in all, with a root module. Answers how
/// much it unpacked, or why the bundle is refused.
fn extract(bundle: &[u8], staging: &Path) -> Result<u64, String> {
    let failed = |error: io::Error| format!("cannot be unpacked: {error}");
    let decoder = zstd::Decoder::new(bundle).map_err(failed)?;
    let mut archive = tar::Archive::new(decoder.take(BUNDLE_LIMIT + 1));
    let mut total = 0u64;
    for entry in archive.entries().map_err(failed)? {
        let mut entry = entry.map_err(failed)?;
        let path = entry.path().map_err(failed)?.into_owned();
        if path
            .components()
            .any(|part| !matches!(part, Component::Normal(_) | Component::CurDir))
        {
            return Err(format!("holds `{}`, outside the bundle", path.display()));
        }
        let target = staging.join(&path);
        match entry.header().entry_type() {
            tar::EntryType::Directory => fs::create_dir_all(&target).map_err(failed)?,
            tar::EntryType::Regular => {
                if let Some(parent) = target.parent() {
                    fs::create_dir_all(parent).map_err(failed)?;
                }
                let mut text = Vec::new();
                entry.read_to_end(&mut text).map_err(failed)?;
                total += u64::try_from(text.len()).unwrap_or(u64::MAX);
                fs::write(&target, text).map_err(failed)?;
            }
            _ => {
                return Err(format!(
                    "holds `{}`, which is neither a file nor a directory",
                    path.display()
                ));
            }
        }
    }
    if total > BUNDLE_LIMIT {
        return Err("unpacks to more than a bundle may, 10 megabytes".to_owned());
    }
    if !staging.join("main.fn").is_file() {
        return Err("has no root module, `main.fn`".to_owned());
    }
    Ok(total)
}

impl Fetch for Fetcher {
    fn fetch(&mut self, url: &PackageUrl) -> Result<PathBuf, Diagnostic> {
        let directory = self.root.join("packages").join(url.hash_text());
        if directory.join("main.fn").is_file() {
            return Ok(directory);
        }
        let bytes = self.download(&url.written)?;
        let hash = blake3::hash(&bytes);
        if hash.as_bytes() != &url.hash {
            return Err(Diagnostic::new(format!(
                "the bundle at `{}` is not the one its URL names",
                url.written
            ))
            .note(format!(
                "its bytes hash to {}, and the URL names {}",
                packages::base58(hash.as_bytes()),
                url.hash_text()
            )));
        }
        self.unpack(&bytes, &directory, &url.written)?;
        self.downloaded += 1;
        Ok(directory)
    }
}

/// Whether a redirect may lead to `url`: by the rule a dependency's URL
/// keeps, `https`, or plain `http` only to this computer.
fn allowed(url: &str) -> bool {
    url.strip_prefix("http://").map_or_else(
        || url.starts_with("https://"),
        |rest| {
            let host = rest.split(['/', ':']).next().unwrap_or_default();
            matches!(host, "localhost" | "127.0.0.1" | "[::1]")
        },
    )
}

/// Where `location`, a redirect from `from`, leads.
fn joined(from: &str, location: &str) -> String {
    if location.contains("://") {
        return location.to_owned();
    }
    let after_scheme = from.find("://").map_or(0, |at| at + 3);
    let origin_end = from[after_scheme..]
        .find('/')
        .map_or(from.len(), |at| after_scheme + at);
    if location.starts_with('/') {
        format!("{}{location}", &from[..origin_end])
    } else {
        let directory = from
            .rfind('/')
            .filter(|&at| at >= origin_end)
            .unwrap_or(origin_end);
        format!("{}/{location}", &from[..directory])
    }
}

/// Make the files under `directory` read-only, as a cached package is.
fn read_only(directory: &Path) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            read_only(&path);
        } else if let Ok(metadata) = fs::metadata(&path) {
            let mut permissions = metadata.permissions();
            permissions.set_readonly(true);
            let _ = fs::set_permissions(&path, permissions);
        }
    }
}

/// Remove staging directories a killed process left: those a day old.
fn clear_stale(staging: &Path) {
    let Ok(entries) = fs::read_dir(staging) else {
        return;
    };
    for entry in entries.flatten() {
        let old = entry
            .metadata()
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(|modified| modified.elapsed().ok())
            .is_some_and(|age| age > STALE);
        if old {
            let _ = fs::remove_dir_all(entry.path());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_redirect_is_read_from_where_it_was_given() {
        let from = "https://example.com/a/b/x.tar.zst";
        assert_eq!(
            joined(from, "https://cdn.example.com/y"),
            "https://cdn.example.com/y"
        );
        assert_eq!(joined(from, "/y"), "https://example.com/y");
        assert_eq!(joined(from, "y"), "https://example.com/a/b/y");
        assert!(allowed("http://localhost:8000/y"));
        assert!(!allowed("http://example.com/y"));
        assert!(allowed("https://example.com/y"));
    }
}
