//! `faun bundle`: a package as one file, named by its hash, for a URL
//! dependency to name.
//!
//! The bundle is a tar archive compressed with zstd, holding the package's
//! root module as `main.fn` at its top and every module the root imports at
//! its path from the root. Each entry is written alike wherever it is made,
//! in order, owned by no one and dated to the epoch, so a package bundled
//! twice is the same bytes. The root's header gets the compiler's language
//! version where it names none, since a bundle never changes.

use std::fs;
use std::path::{Path, PathBuf};

use faun_core::targets::Target;
use faun_frontend::ast::{HeaderValue, Item};
use faun_frontend::diagnostic::Diagnostic;
use faun_frontend::packages::{self, PackageUrl};

use crate::fetch::Fetcher;

/// How hard zstd works: the most it offers short of its slowest levels.
const LEVEL: i32 = 19;

/// Bundle the package at `source` into `directory`, and say where.
pub(crate) fn bundle(
    source: &Path,
    directory: &Path,
    target: &dyn Target,
) -> Result<PathBuf, Diagnostic> {
    let packages = Fetcher::new()?.resolve(source)?;
    let modules = faun_frontend::package_modules(source, target, &packages)?;
    for (name, written, _, _) in packages::dependencies(&modules[0].0)? {
        if !PackageUrl::is_url(&written) {
            return Err(Diagnostic::new(format!(
                "the package depends on `{name}` by a path, `{written}`, which a bundle cannot hold"
            ))
            .help("bundle that package too, and name it by its URL"));
        }
    }
    let mut files = files(&modules)?;
    files.sort();
    let bytes = archive(&files)?;
    let hash = packages::base58(blake3::hash(&bytes).as_bytes());
    fs::create_dir_all(directory).map_err(|error| {
        Diagnostic::new(format!(
            "cannot write into `{}`: {error}",
            directory.display()
        ))
    })?;
    let written = directory.join(format!("{hash}.tar.zst"));
    fs::write(&written, bytes).map_err(|error| {
        Diagnostic::new(format!("cannot write `{}`: {error}", written.display()))
    })?;
    Ok(written)
}

/// Each file of the bundle of `modules`, the root first: its path in the
/// bundle and its text.
fn files(modules: &[(PathBuf, String)]) -> Result<Vec<(String, String)>, Diagnostic> {
    let (root, root_text) = &modules[0];
    let base = root.parent().unwrap_or_else(|| Path::new("."));
    let mut files = vec![("main.fn".to_owned(), versioned(root_text)?)];
    for (path, text) in &modules[1..] {
        let relative = path
            .strip_prefix(base)
            .map_err(|_| {
                Diagnostic::new(format!(
                    "`{}` is outside the package's directory",
                    path.display()
                ))
            })?
            .to_string_lossy()
            .replace('\\', "/");
        if relative == "main.fn" {
            return Err(Diagnostic::new(
                "the package has a module `main.fn` beside its root, which a bundle names so",
            )
            .help("rename it, or make it the root"));
        }
        files.push((relative, text.clone()));
    }
    Ok(files)
}

/// `text`, a root module, with the compiler's language version in its
/// header where it names none.
fn versioned(text: &str) -> Result<String, Diagnostic> {
    let module = faun_frontend::parse(text).map_err(|error| Diagnostic::new(error.message))?;
    let header = module.items.iter().find_map(|item| match item {
        Item::Header(header) => Some(header),
        _ => None,
    });
    let version = concat!(
        "faun: \"",
        env!("CARGO_PKG_VERSION_MAJOR"),
        ".",
        env!("CARGO_PKG_VERSION_MINOR"),
        "\""
    );
    let Some(header) = header else {
        return Ok(format!("package {{{version}}}\n\n{text}"));
    };
    let named = header.fields.iter().any(|field| {
        field.name.text(text) == "faun" && matches!(field.value, HeaderValue::Text(_))
    });
    if named {
        return Ok(text.to_owned());
    }
    let start = usize::try_from(header.span.start).expect("a span fits usize");
    let open = start + text[start..].find('{').expect("a header opens");
    let after = &text[open + 1..];
    let inserted = if after.starts_with('\n') {
        format!("\n  {version},")
    } else if after.trim_start().starts_with('}') {
        version.to_owned()
    } else {
        format!("{version}, ")
    };
    Ok(format!("{}{inserted}{after}", &text[..=open]))
}

/// `files` as a tar archive compressed with zstd, each entry written alike
/// wherever it is made.
fn archive(files: &[(String, String)]) -> Result<Vec<u8>, Diagnostic> {
    let failed =
        |error: std::io::Error| Diagnostic::new(format!("cannot write the bundle: {error}"));
    let mut builder = tar::Builder::new(Vec::new());
    builder.mode(tar::HeaderMode::Deterministic);
    for (path, text) in files {
        let mut header = tar::Header::new_ustar();
        header.set_entry_type(tar::EntryType::Regular);
        header.set_size(u64::try_from(text.len()).unwrap_or(u64::MAX));
        header.set_mode(0o644);
        header.set_mtime(0);
        header.set_uid(0);
        header.set_gid(0);
        builder
            .append_data(&mut header, path, text.as_bytes())
            .map_err(failed)?;
    }
    let tarred = builder.into_inner().map_err(failed)?;
    zstd::encode_all(tarred.as_slice(), LEVEL).map_err(failed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bundled_root_says_which_language_version_it_is_written_for() {
        let version = concat!(
            "\"",
            env!("CARGO_PKG_VERSION_MAJOR"),
            ".",
            env!("CARGO_PKG_VERSION_MINOR"),
            "\""
        );
        assert_eq!(
            versioned("double(n) -> n * 2\n").unwrap(),
            format!("package {{faun: {version}}}\n\ndouble(n) -> n * 2\n")
        );
        assert_eq!(
            versioned("package {}\n").unwrap(),
            format!("package {{faun: {version}}}\n")
        );
        assert_eq!(
            versioned("package {uses: {}}\n").unwrap(),
            format!("package {{faun: {version}, uses: {{}}}}\n")
        );
        assert_eq!(
            versioned("package {\n  uses: {},\n}\n").unwrap(),
            format!("package {{\n  faun: {version},\n  uses: {{}},\n}}\n")
        );
        assert_eq!(
            versioned("package {faun: \"0.0\"}\n").unwrap(),
            "package {faun: \"0.0\"}\n"
        );
    }
}
