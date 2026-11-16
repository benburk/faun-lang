//! URL dependencies, end to end: `faun bundle` writes a package as a file
//! named by its hash, a server on this computer serves it, and `faun`
//! fetches it into a cache of its own and builds against it.

use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::thread;

/// A directory of its own, removed when dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Self {
        let directory =
            std::env::temp_dir().join(format!("faun-urls-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        Self(directory)
    }

    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, text).unwrap();
        path
    }

    /// `faun` with these arguments, fetching into this directory's cache.
    fn faun(&self, arguments: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(arguments)
            .env("FAUN_CACHE", self.0.join("cache"))
            .output()
            .unwrap()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Serve the files under `root` at `/files/…`, and redirect `/moved/…` to
/// them, on this computer, until the test ends. Answers the address.
fn serve(root: &Path) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let address = format!("http://{}", listener.local_addr().unwrap());
    let root = root.to_path_buf();
    thread::spawn(move || {
        for stream in listener.incoming().flatten() {
            answer(stream, &root);
        }
    });
    address
}

fn answer(mut stream: TcpStream, root: &Path) {
    let mut reader = BufReader::new(stream.try_clone().unwrap());
    let mut line = String::new();
    reader.read_line(&mut line).unwrap();
    let path = line.split_whitespace().nth(1).unwrap_or("/").to_owned();
    loop {
        let mut header = String::new();
        if reader.read_line(&mut header).unwrap_or(0) == 0 || header == "\r\n" {
            break;
        }
    }
    if let Some(rest) = path.strip_prefix("/moved/") {
        let response = format!(
            "HTTP/1.1 302 Found\r\nLocation: /files/{rest}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
        );
        let _ = stream.write_all(response.as_bytes());
        return;
    }
    let file = path.strip_prefix("/files/").map(|rest| root.join(rest));
    match file.and_then(|file| fs::read(file).ok()) {
        Some(body) => {
            let head = format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                body.len()
            );
            let _ = stream.write_all(head.as_bytes());
            let _ = stream.write_all(&body);
        }
        None => {
            let _ = stream.write_all(
                b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
            );
        }
    }
}

const LIBRARY: &str = "package {}\n\nimport area {square}\n\nexport {double_square}\n\n\
     double_square : Nat -> Nat\ndouble_square(n) -> square(n) * 2\n";

const AREA: &str = "export {square}\n\nsquare : Nat -> Nat\nsquare(n) -> n * n\n";

/// Bundle the library into `served/shapes/1.0.0/`, and answer the bundle's
/// file name.
fn bundled(scratch: &Scratch) -> String {
    let root = scratch.write("library/shapes.fn", LIBRARY);
    scratch.write("library/area.fn", AREA);
    let into = scratch.0.join("served/shapes/1.0.0");
    let output = scratch.faun(&[
        "bundle",
        root.to_str().unwrap(),
        "-o",
        into.to_str().unwrap(),
    ]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut names: Vec<String> = fs::read_dir(&into)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    assert_eq!(names.len(), 1);
    names.remove(0)
}

fn app(scratch: &Scratch, url: &str) -> PathBuf {
    scratch.write(
        "app/main.fn",
        &format!(
            "package {{\n  uses: {{shapes: \"{url}\"}},\n}}\n\nimport shapes {{double_square}}\n\n\
             eight : Nat\neight = double_square(2)\n\nexpect eight == 8\n"
        ),
    )
}

#[test]
fn a_package_is_bundled_served_fetched_and_built_against() {
    let scratch = Scratch::new("served");
    let bundle = bundled(&scratch);
    let again = bundled(&scratch);
    assert_eq!(bundle, again, "bundling twice writes the same bytes");
    let address = serve(&scratch.0.join("served"));
    let url = format!("{address}/files/shapes/1.0.0/{bundle}");
    let entry = app(&scratch, &url);
    let entry = entry.to_str().unwrap();
    let checked = scratch.faun(&["check", entry]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    let cached = scratch
        .0
        .join("cache/packages")
        .join(bundle.trim_end_matches(".tar.zst"));
    let root = fs::read_to_string(cached.join("main.fn")).unwrap();
    assert!(root.starts_with("package {faun: \""), "{root}");
    assert!(cached.join("area.fn").is_file());
    let used = scratch.faun(&["uses", entry]);
    let used = String::from_utf8_lossy(&used.stdout);
    assert!(used.contains(&format!("shapes: {url}")), "{used}");
    // Cached, it is read again with no server to ask.
    fs::remove_dir_all(scratch.0.join("served")).unwrap();
    let offline = scratch.faun(&["check", entry]);
    assert!(
        offline.status.success(),
        "{}",
        String::from_utf8_lossy(&offline.stderr)
    );
}

#[test]
fn a_redirect_is_followed_and_a_bundle_not_the_one_named_is_refused() {
    let scratch = Scratch::new("redirect");
    let bundle = bundled(&scratch);
    let address = serve(&scratch.0.join("served"));
    let moved = app(&scratch, &format!("{address}/moved/shapes/1.0.0/{bundle}"));
    let checked = scratch.faun(&["check", moved.to_str().unwrap()]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );

    let other = Scratch::new("redirect-other");
    let wrong = format!("{}.tar.zst", "1".repeat(32));
    let served = scratch.0.join("served/shapes/1.0.0");
    fs::copy(served.join(&bundle), served.join(&wrong)).unwrap();
    let entry = app(&other, &format!("{address}/files/shapes/1.0.0/{wrong}"));
    let refused = other.faun(&["check", entry.to_str().unwrap()]);
    let said = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success());
    assert!(said.contains("is not the one its URL names"), "{said}");
}

#[test]
fn a_bundle_holds_no_path_dependency() {
    let scratch = Scratch::new("paths");
    scratch.write("library/area.fn", AREA);
    let root = scratch.write(
        "library/shapes.fn",
        "package {uses: {area: \"area\"}}\n\nimport area {square}\n",
    );
    let output = scratch.faun(&["bundle", root.to_str().unwrap(), "-o", "/nowhere"]);
    let said = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(said.contains("which a bundle cannot hold"), "{said}");
}
