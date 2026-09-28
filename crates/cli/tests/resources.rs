//! Resources, which a program uses up exactly once: an open file closed, or
//! answered to whoever closes it, on every way a function goes on. What each
//! function does with a file it is handed is found from its body.

mod support;

use std::path::PathBuf;

use support::{Directory, Package};

fn example(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../faun/examples/files")
        .join(name)
}

/// A file read and another written, each closed: what was read is what is
/// written, and a file that is not there is `NotFound`.
#[test]
fn copy_reads_one_file_into_another() {
    let text = b"hello file\n".to_vec();
    let files = [("input.txt".to_owned(), text.clone())].into();
    let (status, written, left) = support::run_among(&example("copy.fn"), files);
    assert_eq!((status, written.as_str()), (0, "copied\n"));
    assert_eq!(left["output.txt"], text);
    let (status, _, left) = support::run_among(&example("copy.fn"), Directory::new());
    assert_eq!((status, left), (2, Directory::new()));
}

/// Files travel in lists, split and merged, and are each closed once.
#[test]
fn files_travel_in_lists_and_are_each_closed_once() {
    let (status, _, left) = support::run_among(&example("resource-list.fn"), Directory::new());
    assert_eq!(status, 0);
    assert_eq!(left.keys().collect::<Vec<_>>(), ["a.tmp", "b.tmp"]);
}

/// Functions that only lend what they are handed may leave by `?` while
/// they hold it: the one that opened it closes it.
#[test]
fn a_lent_file_may_be_held_where_a_function_leaves() {
    let text = "héllo wörld\n".as_bytes().to_vec();
    let files = [("input.txt".to_owned(), text.clone())].into();
    let (status, written, left) = support::run_among(&example("trickle.fn"), files);
    assert_eq!((status, written.as_str()), (0, "trickled\n"));
    assert_eq!(left["output.txt"], text);
}

/// A name holding a nought byte is refused before the target is asked,
/// which would read it as ending there: nothing named by its front is made.
#[test]
fn a_name_holding_a_nought_byte_is_refused() {
    let package = Package::new(
        "nought-name",
        "import std.host {Host, File, IoError, Mode.*}

         main! : Host -> []
         main!(host) ->
           opened = host.files.open!(\"bad\\0name\", Overwrite)
           status = shut!(opened)
           host.exit!(U8.of_nat(status))

         shut! : Result(File, IoError) -> Nat
         shut!(Ok(file)) ->
           closed = file.close!()
           0
         shut!(Err(Other(_))) -> 6
         shut!(Err(_)) -> 7",
    );
    let (status, _, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!((status, left), (6, Directory::new()));
}
