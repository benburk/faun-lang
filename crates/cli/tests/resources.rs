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

/// What opens a file and what is refused of it, each with what is wrong.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "a file opened and never closed",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           Ok(0)",
        "the `File` `Files.open!` answers is neither used up nor answered on every way `program!` goes on",
    ),
    (
        "a file opened on a line of its own",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           files.open!(\"a.txt\", Read)
           Ok(0)",
        "the `File` `Files.open!` answers is neither used up",
    ),
    (
        "a file held where `?` leaves",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           bytes = file.read!(4)?
           closed = file.close!()
           Ok(0)",
        "the `File` `Files.open!` answers is neither used up",
    ),
    (
        "a file read after it is closed",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           closed = file.close!()
           bytes = file.read!(4)
           Ok(0)",
        "this `File` has already been used up",
    ),
    (
        "a file closed twice in one call",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           closed = both!(file, file)
           Ok(0)

         both! : (File, File) -> Nat
         both!(a, b) ->
           x = a.close!()
           y = b.close!()
           0",
        "this `File` has already been used up",
    ),
    (
        "a file closed on one way a function goes on and kept on another",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           n = maybe!(file, 1)
           Ok(n)

         maybe! : (File, Nat) -> Nat
         maybe!(file, 0) ->
           closed = file.close!()
           0
         maybe!(_, _) -> 1",
        "`maybe!` uses up the `File` its parameter 1 holds on one way it goes on and not on another",
    ),
    (
        "a file a function is handed, held where its `?` leaves, is its fault and not its caller's",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           used = use!(file)
           Ok(0)

         use! : File -> Result(Nat, IoError)
         use!(file) ->
           bytes = file.read!(4)?
           closed = file.close!()?
           Ok(0)",
        "`use!` uses up the `File` its parameter 1 holds on one way it goes on and not on another",
    ),
    (
        "a file closed on only some ways, handed on through another, is refused where it is closed",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           n = through!(file)
           Ok(n)

         through! : File -> Nat
         through!(file) -> maybe!(file, 3)

         maybe! : (File, Nat) -> Nat
         maybe!(_, 0) -> 0
         maybe!(file, n) ->
           closed = file.close!()
           n",
        "`maybe!` uses up the `File` its parameter 1 holds on one way it goes on and not on another",
    ),
    (
        "a file taken by a guard",
        "program! : Files -> Result(Nat, IoError)
         program!(files) ->
           file = files.open!(\"a.txt\", Read)?
           n = asked!(file)
           Ok(n)

         held : File -> List(File)
         held(file) -> [file]

         asked! : File -> Nat
         asked!(file) if held(file).is_empty() -> 0
         asked!(file) ->
           closed = file.close!()
           1",
        "a guard only looks, and this uses up a resource",
    ),
];

#[test]
fn what_a_program_does_with_a_file_is_checked() {
    for (name, body, expected) in REFUSED {
        let source = format!(
            "import std.host {{Files, File, IoError, Mode.*}}

             main! : Host -> []
             main!(host) ->
               ran = program!(host.files)
               host.exit!(0)

             {}",
            body.trim_start()
        );
        let refused = Package::new(name, &source).refusal();
        assert!(refused.contains(expected), "{name}: {refused}");
    }
}
