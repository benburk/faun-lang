//! URL dependencies: what a URL names, and which package each URL a build's
//! headers write is read from.
//!
//! A URL names a bundle by the BLAKE3 hash of its bytes, in base58, as its
//! last segment before `.tar.zst`, and may hold one version,
//! `MAJOR.MINOR.PATCH`, anywhere before it. URLs that differ only in their
//! version and hash are versions of one package. Within a build, versions of
//! one package with one major, or below `1.0.0` one minor, are compatible,
//! and every header naming one is read as naming the highest version
//! mentioned: a fixed point over the chosen versions' own dependencies, not
//! a search. The package being built uses its own dependencies as written,
//! and a higher version wanted deeper is refused, with the chain that wants
//! it.
//!
//! Fetching is not this crate's: [`resolve`] asks a [`Fetch`] for the
//! directory a bundle is unpacked in, and the loader reads a URL dependency
//! from there.

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use crate::ast::Item;
use crate::diagnostic::{Diagnostic, Location};
use crate::modules::{decoded, header_fields, module_base};
use crate::{Sources, parse_in};

/// The base58 alphabet Bitcoin uses, which has no `0`, `O`, `I` or `l`.
const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/// `bytes` in base58, each leading zero byte a leading `1`.
///
/// # Panics
/// Never: a remainder of 58 fits a byte.
#[must_use]
pub fn base58(bytes: &[u8]) -> String {
    let mut digits: Vec<u8> = Vec::new();
    for &byte in bytes {
        let mut carry = u32::from(byte);
        for digit in &mut digits {
            carry += u32::from(*digit) << 8;
            *digit = u8::try_from(carry % 58).expect("a remainder of 58 fits a byte");
            carry /= 58;
        }
        while carry > 0 {
            digits.push(u8::try_from(carry % 58).expect("a remainder of 58 fits a byte"));
            carry /= 58;
        }
    }
    let zeros = bytes.iter().take_while(|&&byte| byte == 0).count();
    let ones = std::iter::repeat_n('1', zeros);
    ones.chain(
        digits
            .iter()
            .rev()
            .map(|&digit| char::from(ALPHABET[usize::from(digit)])),
    )
    .collect()
}

/// The bytes `text` spells in base58, where it is base58.
fn from_base58(text: &str) -> Option<Vec<u8>> {
    let mut bytes: Vec<u8> = Vec::new();
    for character in text.bytes() {
        let mut carry = u32::try_from(ALPHABET.iter().position(|&c| c == character)?).ok()?;
        for byte in &mut bytes {
            carry += u32::from(*byte) * 58;
            *byte = u8::try_from(carry & 0xff).expect("masked to a byte");
            carry >>= 8;
        }
        while carry > 0 {
            bytes.push(u8::try_from(carry & 0xff).expect("masked to a byte"));
            carry >>= 8;
        }
    }
    let ones = text.bytes().take_while(|&c| c == b'1').count();
    bytes.extend(std::iter::repeat_n(0, ones));
    bytes.reverse();
    Some(bytes)
}

/// `MAJOR.MINOR.PATCH`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
}

impl Version {
    /// What a compatible version shares: its major, or below `1.0.0` its
    /// minor too.
    const fn compatibility(self) -> (u64, u64) {
        if self.major == 0 {
            (0, self.minor)
        } else {
            (self.major, 0)
        }
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// A dependency written as a URL to a bundle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageUrl {
    /// As the header wrote it.
    pub written: String,
    /// The BLAKE3 hash of the bundle's bytes.
    pub hash: [u8; 32],
    pub version: Option<Version>,
    /// What every version of the package shares: the URL with its version
    /// and its hash's segment left out.
    package: String,
}

impl PackageUrl {
    /// The hash in base58, as the URL writes it.
    #[must_use]
    pub fn hash_text(&self) -> String {
        base58(&self.hash)
    }

    /// Whether `written` is a URL rather than a path: anything with a
    /// scheme, `https://`.
    #[must_use]
    pub fn is_url(written: &str) -> bool {
        crate::modules::url_scheme(written).is_some()
    }

    /// Read a URL dependency.
    ///
    /// # Errors
    /// Says why `written` names no bundle: a scheme other than `https`, or
    /// `http` to another computer than this one, no hash, a query, or more
    /// than one version.
    pub fn parse(written: &str) -> Result<Self, String> {
        let rest = after_scheme(written)?;
        if rest.contains(['?', '#']) {
            return Err("has a query or a fragment, which a bundle's URL does not".to_owned());
        }
        let (before, last) = rest
            .rsplit_once('/')
            .ok_or_else(|| "names no bundle: its last segment is `HASH.tar.zst`".to_owned())?;
        let hash = last
            .strip_suffix(".tar.zst")
            .and_then(from_base58)
            .and_then(|bytes| <[u8; 32]>::try_from(bytes).ok())
            .ok_or_else(|| {
                format!(
                    "names no bundle: its last segment, `{last}`, is not a BLAKE3 hash in base58 followed by `.tar.zst`"
                )
            })?;
        let versions = versions(before);
        if versions.len() > 1 {
            return Err("holds more than one version".to_owned());
        }
        let scheme = &written[..written.len() - rest.len()];
        let (version, package) = match versions.first() {
            Some(&(start, end, version)) => (
                Some(version),
                format!("{scheme}{}*{}", &before[..start], &before[end..]),
            ),
            None => (None, format!("{scheme}{before}/{last}")),
        };
        Ok(Self {
            written: written.to_owned(),
            hash,
            version,
            package,
        })
    }

    /// Which versions this one is chosen among: none, for a URL with no
    /// version, which is its own package.
    fn group(&self) -> Option<Group> {
        let version = self.version?;
        Some((self.package.clone(), version.compatibility()))
    }
}

/// What follows the scheme of `written`, where it is one a dependency may
/// be fetched by: `https`, or plain `http` to this computer, for testing.
fn after_scheme(written: &str) -> Result<&str, String> {
    if let Some(rest) = written.strip_prefix("https://") {
        return Ok(rest);
    }
    if let Some(rest) = written.strip_prefix("http://") {
        let host = rest.split(['/', ':']).next().unwrap_or_default();
        if !matches!(host, "localhost" | "127.0.0.1" | "[::1]") {
            return Err("is plain `http`, which only `localhost` may serve".to_owned());
        }
        return Ok(rest);
    }
    let scheme = crate::modules::url_scheme(written).unwrap_or("?");
    Err(format!(
        "is a `{scheme}://` URL, and only `https` is fetched"
    ))
}

/// Every `MAJOR.MINOR.PATCH` in `text`, where it starts and ends, each not
/// part of a longer run of digits and dots.
fn versions(text: &str) -> Vec<(usize, usize, Version)> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        if !bytes[at].is_ascii_digit() || at > 0 && matches!(bytes[at - 1], b'0'..=b'9' | b'.') {
            at += 1;
            continue;
        }
        let end = at
            + bytes[at..]
                .iter()
                .take_while(|byte| byte.is_ascii_digit() || **byte == b'.')
                .count();
        let parts: Vec<&str> = text[at..end].split('.').collect();
        if let [major, minor, patch] = parts[..]
            && let (Ok(major), Ok(minor), Ok(patch)) = (major.parse(), minor.parse(), patch.parse())
        {
            found.push((
                at,
                end,
                Version {
                    major,
                    minor,
                    patch,
                },
            ));
        }
        at = end;
    }
    found
}

/// What gets the bundle a URL names, unpacked: the directory holding its
/// root module, `main.fn`.
pub trait Fetch {
    /// # Errors
    /// Says why the bundle cannot be had.
    fn fetch(&mut self, url: &PackageUrl) -> Result<PathBuf, Diagnostic>;
}

/// Which package every URL a build's headers write is read from.
#[derive(Clone, Debug, Default)]
pub struct Packages {
    /// Each URL as written, and the root module it is read from: its chosen
    /// version's.
    urls: HashMap<String, PathBuf>,
    /// The dependency graph as a tree, for `faun uses`.
    pub tree: Vec<Use>,
}

impl Packages {
    /// The root module a URL dependency, as written, is read from.
    #[must_use]
    pub fn root(&self, written: &str) -> Option<&Path> {
        self.urls.get(written).map(PathBuf::as_path)
    }
}

/// One dependency in the tree of what a package uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Use {
    /// How many packages lie between it and the package being built.
    pub depth: usize,
    /// The name its depending package imports it as.
    pub name: String,
    /// The URL or path its header wrote.
    pub written: String,
    /// The version chosen in its place, where another was.
    pub chosen: Option<Version>,
    /// Whether it was shown before, so its own dependencies are not again.
    pub shown: bool,
    /// Whether its header names it in `test_uses`.
    pub for_tests: bool,
}

/// Which versions a versioned URL is chosen among: what every version of
/// its package shares, and what its compatible versions share.
type Group = (String, (u64, u64));

/// How many times choosing may go round before it is refused as not
/// settling.
const ROUNDS: usize = 64;

/// Choose a version for every versioned URL the package at `entry` reaches,
/// fetching each package choosing reads, and say which package every URL
/// is read from.
///
/// A dependency's own `test_uses` are fetched as written: they are no part
/// of what the build chooses.
///
/// # Errors
/// Reports a header that cannot be read, a URL that names no bundle, a
/// bundle that cannot be fetched, a higher version wanted than the package
/// being built writes, two bundles for one version, and choosing that does
/// not settle.
pub fn resolve(entry: &Path, fetch: &mut dyn Fetch) -> Result<Packages, Diagnostic> {
    let mut chosen: BTreeMap<Group, PackageUrl> = BTreeMap::new();
    for _ in 0..ROUNDS {
        let mut walk = Walk {
            fetch: &mut *fetch,
            chosen: &chosen,
            mentions: BTreeMap::new(),
            urls: HashMap::default(),
            visited: HashSet::default(),
            tree: Vec::new(),
        };
        walk.package(entry, &mut vec![root_name(entry)], 0, true)?;
        let Walk {
            mentions,
            urls,
            tree,
            ..
        } = walk;
        let next = choose(mentions)?;
        if next == chosen {
            return Ok(Packages { urls, tree });
        }
        chosen = next;
    }
    Err(Diagnostic::new(
        "choosing versions does not settle: each choice brings in packages that want another",
    ))
}

/// The version each group's `mentions` choose: the highest, or the one the
/// package being built writes, which may not be lower.
fn choose(
    mentions: BTreeMap<Group, Vec<Mention>>,
) -> Result<BTreeMap<Group, PackageUrl>, Diagnostic> {
    let mut chosen = BTreeMap::new();
    for (group, mentioned) in mentions {
        let highest = highest(&mentioned)?;
        let own = mentioned.iter().find(|mention| mention.by_root);
        if let Some(own) = own
            && own.url.version < highest.url.version
        {
            return Err(Diagnostic::new(format!(
                "{} wants `{}`, newer than the `{}` this package depends on",
                highest.chain.join(" → "),
                highest.url.written,
                own.url.written,
            ))
            .help("depend on the newer version, or on an older version of what wants it"));
        }
        chosen.insert(group, own.unwrap_or(highest).url.clone());
    }
    Ok(chosen)
}

/// The highest version `mentioned`, refusing two bundles for it.
fn highest(mentioned: &[Mention]) -> Result<&Mention, Diagnostic> {
    let highest = mentioned
        .iter()
        .max_by_key(|mention| mention.url.version)
        .expect("a group is mentioned at least once");
    if let Some(other) = mentioned.iter().find(|mention| {
        mention.url.version == highest.url.version && mention.url.hash != highest.url.hash
    }) {
        let version = highest.url.version.expect("a group's versions are written");
        return Err(Diagnostic::new(format!(
            "version {version} is named by two bundles: `{}` and `{}`",
            highest.url.written, other.url.written
        ))
        .note("a version is one bundle, so its hash names it"));
    }
    Ok(highest)
}

/// A versioned URL a header writes, and the chain of packages that reaches
/// it.
struct Mention {
    url: PackageUrl,
    chain: Vec<String>,
    by_root: bool,
}

/// One round of choosing: every package the chosen versions reach.
struct Walk<'a> {
    fetch: &'a mut dyn Fetch,
    chosen: &'a BTreeMap<Group, PackageUrl>,
    mentions: BTreeMap<Group, Vec<Mention>>,
    urls: HashMap<String, PathBuf>,
    visited: HashSet<PathBuf>,
    tree: Vec<Use>,
}

impl Walk<'_> {
    /// Walk the dependencies of the package whose root module is `root`.
    fn package(
        &mut self,
        root: &Path,
        chain: &mut Vec<String>,
        depth: usize,
        is_root: bool,
    ) -> Result<(), Diagnostic> {
        let directory = root.parent().unwrap_or_else(|| Path::new("."));
        for (name, written, for_tests, at) in dependencies(root)? {
            // A dependency's tests are its own, so what they use is fetched
            // as written and chooses nothing.
            let chooses = is_root || !for_tests;
            let (module, chosen) = if PackageUrl::is_url(&written) {
                let mut wanted_by = chain.clone();
                wanted_by.push(format!("`{name}`"));
                self.url(&written, wanted_by, is_root, chooses)
                    .map_err(|diagnostic| match diagnostic.location() {
                        Some(_) => diagnostic,
                        None => diagnostic.at_location(at),
                    })?
            } else {
                // A path that finds no module is the loader's to report.
                let Ok(module) = module_base(directory, &directory.join(&written)) else {
                    continue;
                };
                (module, None)
            };
            let identity = module.canonicalize().unwrap_or_else(|_| module.clone());
            let shown = !self.visited.insert(identity);
            self.tree.push(Use {
                depth,
                name: name.clone(),
                written,
                chosen,
                shown,
                for_tests,
            });
            if !shown {
                chain.push(format!("`{name}`"));
                self.package(&module, chain, depth + 1, false)?;
                chain.pop();
            }
        }
        Ok(())
    }
}

impl Walk<'_> {
    /// Fetch the version chosen for the URL dependency `written`, which
    /// `chain` reaches, noting it among what chooses where it does: the root
    /// module it is read from, and the version chosen in its place.
    fn url(
        &mut self,
        written: &str,
        chain: Vec<String>,
        by_root: bool,
        chooses: bool,
    ) -> Result<(PathBuf, Option<Version>), Diagnostic> {
        let name = chain.last().cloned().unwrap_or_default();
        let url = PackageUrl::parse(written)
            .map_err(|message| Diagnostic::new(format!("dependency {name} {message}")))?;
        let group = url.group().filter(|_| chooses);
        let used = group
            .as_ref()
            .and_then(|group| self.chosen.get(group))
            .unwrap_or(&url)
            .clone();
        if let Some(group) = group {
            self.mentions.entry(group).or_default().push(Mention {
                url: url.clone(),
                chain,
                by_root,
            });
        }
        let module = self.fetch.fetch(&used)?.join("main.fn");
        self.urls.insert(written.to_owned(), module.clone());
        let chosen = (used.version != url.version)
            .then_some(used.version)
            .flatten();
        Ok((module, chosen))
    }
}

/// How a chain names the package being built.
fn root_name(entry: &Path) -> String {
    format!("`{}`", entry.display())
}

/// The dependencies the header of the root module at `root` names: each
/// one's name, how it is written, whether it is in `test_uses`, and where
/// the header names it.
///
/// A module with a syntax error names none: the loader reports it.
///
/// # Errors
/// Reports a root module that cannot be read, or whose header's fields are
/// wrong.
///
/// # Panics
/// Never: the source it reads is the one it adds.
pub fn dependencies(root: &Path) -> Result<Vec<(String, String, bool, Location)>, Diagnostic> {
    let text = std::fs::read_to_string(root)
        .map_err(|error| Diagnostic::new(format!("cannot read `{}`: {error}", root.display())))?;
    let mut sources = Sources::default();
    let source = sources.add(root.to_path_buf(), text.clone());
    let file = sources.get(source).expect("the source just added");
    // A module that cannot be read is the loader's to report, with all it
    // has to say.
    let Ok(module) = parse_in(&text, source) else {
        return Ok(Vec::new());
    };
    let Some(header) = module.items.iter().find_map(|item| match item {
        Item::Header(header) => Some(header),
        _ => None,
    }) else {
        return Ok(Vec::new());
    };
    header_fields(header, file)?
        .into_iter()
        .map(|(dependency, for_tests)| {
            let written = decoded(&dependency.path, file)
                .map_err(|message| Diagnostic::new(message).at(file, dependency.span))?;
            Ok((
                dependency.name.text(&text).to_owned(),
                written,
                for_tests,
                Location::of(file, dependency.span),
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base58_reads_back_what_it_writes() {
        for bytes in [&[][..], &[0], &[0, 0, 1], &[255; 32], b"hello world"] {
            assert_eq!(from_base58(&base58(bytes)).unwrap(), bytes);
        }
        assert_eq!(base58(b"hello world"), "StV1DL6CwTryKyV");
        assert_eq!(from_base58("0OIl"), None);
    }

    fn url(written: &str) -> Result<PackageUrl, String> {
        PackageUrl::parse(written)
    }

    #[test]
    fn a_url_names_its_bundle_by_hash_and_may_hold_one_version() {
        let hash = base58(&[7; 32]);
        let one = url(&format!("https://example.com/pcg/1.2.0/{hash}.tar.zst")).unwrap();
        assert_eq!(
            one.version,
            Some(Version {
                major: 1,
                minor: 2,
                patch: 0
            })
        );
        assert_eq!(one.hash, [7; 32]);
        let two = url(&format!("https://example.com/pcg/1.4.1/{hash}.tar.zst")).unwrap();
        assert_eq!(one.group(), two.group());
        let next = url(&format!("https://example.com/pcg/2.0.0/{hash}.tar.zst")).unwrap();
        assert_ne!(one.group(), next.group());
        let early = url(&format!("https://example.com/pcg-0.3.0/{hash}.tar.zst")).unwrap();
        let later = url(&format!("https://example.com/pcg-0.4.0/{hash}.tar.zst")).unwrap();
        assert_ne!(early.group(), later.group());
        let bare = url(&format!("https://example.com/pcg/{hash}.tar.zst")).unwrap();
        assert_eq!(bare.version, None);
        assert_eq!(bare.group(), None);
        url(&format!("http://localhost:8000/{hash}.tar.zst")).unwrap();
    }

    /// Packages written to a directory of their own, each URL's bundle one
    /// of them, found by its hash.
    struct World {
        directory: PathBuf,
        bundles: HashMap<[u8; 32], PathBuf>,
        fetched: Vec<String>,
    }

    impl World {
        fn new(name: &str) -> Self {
            let directory =
                std::env::temp_dir().join(format!("faun-versions-{name}-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&directory);
            std::fs::create_dir_all(&directory).unwrap();
            Self {
                directory,
                bundles: HashMap::default(),
                fetched: Vec::new(),
            }
        }

        /// A package at `path` whose header is `header`.
        fn package(&self, path: &str, header: &str) -> PathBuf {
            let root = self.directory.join(path).join("main.fn");
            std::fs::create_dir_all(root.parent().unwrap()).unwrap();
            std::fs::write(&root, format!("package {{uses: {{{header}}}}}\n")).unwrap();
            root
        }

        /// The URL of version `version` of `name`, a bundle whose header is
        /// `header`; `seed` tells two bundles of one version apart.
        fn bundle(&mut self, name: &str, version: &str, seed: u8, header: &str) -> String {
            let hash = [seed; 32];
            let root = self.package(&format!("{name}-{version}-{seed}"), header);
            self.bundles
                .insert(hash, root.parent().unwrap().to_path_buf());
            format!(
                "https://example.com/{name}/{version}/{}.tar.zst",
                base58(&hash)
            )
        }
    }

    impl Drop for World {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.directory);
        }
    }

    impl Fetch for World {
        fn fetch(&mut self, url: &PackageUrl) -> Result<PathBuf, Diagnostic> {
            self.fetched.push(url.written.clone());
            Ok(self.bundles[&url.hash].clone())
        }
    }

    #[test]
    fn every_header_naming_a_package_reads_its_highest_compatible_version() {
        let mut world = World::new("highest");
        let old = world.bundle("lib", "1.2.0", 1, "");
        let new = world.bundle("lib", "1.4.1", 2, "");
        let next = world.bundle("lib", "2.0.0", 3, "");
        let left = world.package("left", &format!("lib: \"{old}\""));
        let right = world.package("right", &format!("lib: \"{new}\", next: \"{next}\""));
        let entry = world.package(
            "app",
            &format!(
                "left: \"{}\", right: \"{}\"",
                left.with_extension("").display(),
                right.with_extension("").display()
            ),
        );
        let packages = resolve(&entry, &mut world).unwrap();
        assert_eq!(packages.root(&old), packages.root(&new));
        assert_ne!(packages.root(&new), packages.root(&next));
        let chosen: Vec<_> = packages
            .tree
            .iter()
            .filter_map(|used| used.chosen)
            .collect();
        assert_eq!(
            chosen,
            [Version {
                major: 1,
                minor: 4,
                patch: 1
            }]
        );
    }

    #[test]
    fn the_package_built_uses_its_own_versions_and_refuses_a_newer_one_wanted() {
        let mut world = World::new("own");
        let old = world.bundle("lib", "0.3.0", 1, "");
        let new = world.bundle("lib", "0.3.5", 2, "");
        let wanting = world.bundle("wants", "1.0.0", 3, &format!("lib: \"{new}\""));
        let entry = world.package("app", &format!("lib: \"{old}\", wants: \"{wanting}\""));
        let error = resolve(&entry, &mut world).unwrap_err();
        assert!(
            error.message.contains("`wants` → `lib` wants"),
            "{}",
            error.message
        );
        assert!(error.message.contains("newer than"), "{}", error.message);
        let fine = world.package("fine", &format!("lib: \"{new}\", wants: \"{wanting}\""));
        resolve(&fine, &mut world).unwrap();
    }

    #[test]
    fn one_version_is_one_bundle() {
        let mut world = World::new("one");
        let first = world.bundle("lib", "1.0.0", 1, "");
        let second = world.bundle("lib", "1.0.0", 2, "");
        let left = world.package("left", &format!("lib: \"{first}\""));
        let entry = world.package(
            "app",
            &format!(
                "left: \"{}\", lib: \"{second}\"",
                left.with_extension("").display()
            ),
        );
        let error = resolve(&entry, &mut world).unwrap_err();
        assert!(
            error.message.contains("named by two bundles"),
            "{}",
            error.message
        );
    }

    #[test]
    fn a_dependency_with_no_version_is_its_own_package() {
        let mut world = World::new("bare");
        let versioned = world.bundle("lib", "1.0.0", 1, "");
        let hash = [9; 32];
        let root = world.package("bare", "");
        world
            .bundles
            .insert(hash, root.parent().unwrap().to_path_buf());
        let bare = format!("https://example.com/lib/{}.tar.zst", base58(&hash));
        let entry = world.package("app", &format!("a: \"{versioned}\", b: \"{bare}\""));
        let packages = resolve(&entry, &mut world).unwrap();
        assert_ne!(packages.root(&versioned), packages.root(&bare));
    }

    #[test]
    fn a_url_that_names_no_bundle_is_refused() {
        let hash = base58(&[7; 32]);
        for (written, said) in [
            (
                format!("http://example.com/{hash}.tar.zst"),
                "only `localhost`",
            ),
            (format!("ftp://example.com/{hash}.tar.zst"), "only `https`"),
            (
                "https://example.com/pcg.tar.zst".to_owned(),
                "not a BLAKE3 hash",
            ),
            (
                format!("https://example.com/{hash}.zip"),
                "not a BLAKE3 hash",
            ),
            (
                format!("https://example.com/1.0.0/2.0.0/{hash}.tar.zst"),
                "more than one version",
            ),
            (format!("https://example.com/{hash}.tar.zst?x=1"), "query"),
        ] {
            let error = url(&written).unwrap_err();
            assert!(error.contains(said), "{written}: {error}");
        }
        assert!(versions("1.2.3.4").is_empty());
    }
}
