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

/// Files opened in a loop are carried out of it in a list, and another
/// loop walking the list writes and closes each; a test and arms take
/// apart what opening answered. A name that does not open is passed over.
#[test]
fn files_opened_in_one_loop_are_closed_in_another() {
    let (status, written, left) = support::run_among(&example("batch.fn"), Directory::new());
    assert_eq!((status, written.as_str()), (2, "a.txt\nb.txt\n"));
    assert_eq!(left.keys().collect::<Vec<_>>(), ["a.txt", "b.txt"]);
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

/// A branch that never answers is a way `main!` ends, so it closes the
/// file it holds there, and has no say in what the branch that answers
/// does with it: that one hands it on to be closed after.
#[test]
fn a_branch_that_never_answers_closes_what_it_holds() {
    let package = Package::new(
        "never-answers",
        "import std.host {Host, Mode.*}

         main! : Host -> []
         main!(host) -> (
           opened = host.files.open!(\"a.txt\", Overwrite)
           opened is (
             Ok(file) then (
               n = if host.args.len() > 1 then 3 else (
                 closed = file.close!()
                 host.exit!(2)
               )
               wrote = file.write_all!(\"never\".to_utf8())
               closed = file.close!()
               host.exit!(U8.of_nat(n))
             )
             Err(_) then host.exit!(4)
           )
         )",
    );
    let (status, written, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!((status, written.as_str()), (2, ""));
    assert_eq!(left["a.txt"], b"");
}

/// A file closed in both branches of an `if` is closed whichever is
/// chosen, so it is used up once on every way the function goes on.
#[test]
fn a_file_closed_in_both_branches_of_an_if_is_closed_once() {
    let package = Package::new(
        "both-branches",
        "import std.host {Host, Files, IoError, Mode.*}

         main! : Host -> []
         main!(host) -> (
           ran = program!(host.files, host.args.len())
           host.exit!(if ran == Ok(1) then 0 else 1)
         )

         program! : (Files, Nat) -> Result(Nat, IoError)
         program!(files, n) -> (
           file = files.open!(\"a.txt\", Overwrite)?
           closed = if n == 0 then file.close!() else file.close!()
           _ = closed?
           Ok(n)
         )",
    );
    let (status, _, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!(status, 0);
    assert_eq!(left.keys().collect::<Vec<_>>(), ["a.txt"]);
}

/// A value holds a file only where a test leaves it able to: an empty list
/// holds none, and neither does a pair whose rows cover every value but
/// those holding no file.
#[test]
fn a_test_showing_a_value_holds_no_file_leaves_nothing_to_close() {
    let package = Package::new(
        "nothing-held",
        "import std.host {Host, File, IoError, Mode.*}

         main! : Host -> []
         main!(host) -> (
           opened = host.files.open!(\"a.txt\", Overwrite)
           other = host.files.open!(\"b.txt\", Overwrite)
           none = close_all!([])
           some = close_all!([other])
           shut = shut!(opened, host.args.len() == 0)
           host.exit!(U8.of_nat(none + some + shut))
         )

         close_all! : List(Result(File, IoError)) -> Nat
         close_all!(files) -> if files is [] then 0 else (
           count = 0
           for opened in files do (
             opened is Ok(file) else continue
             closed = file.close!()
             count = count + 1
           )
           count
         )

         shut! : (Result(File, IoError), Bool) -> Nat
         shut!(opened, quiet) -> (
           pair = (opened, quiet)
           pair is ((Err(_), _) | (_, True) | (_, False)) else return 9
           (result, _) = pair
           result is Ok(file) else return 7
           closed = file.close!()
           2
         )",
    );
    let (status, _, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!(status, 3);
    assert_eq!(left.keys().collect::<Vec<_>>(), ["a.txt", "b.txt"]);
}

/// A record's fields holding files are each held on their own: one is
/// lent, then each closed through its field, and a field holding none read
/// after.
#[test]
fn files_in_a_record_are_used_up_field_by_field() {
    let package = Package::new(
        "record-fields",
        "import std.host {Host, File, IoError, Mode.*}

         main! : Host -> []
         main!(host) -> (
           a = host.files.open!(\"a.txt\", Overwrite)
           b = host.files.open!(\"b.txt\", Overwrite)
           pair = {a, b, count: 3}
           wrote = done!(pair.a)
           closed = done!(pair.b)
           host.exit!(U8.of_nat(wrote + closed + pair.count))
         )

         done! : Result(File, IoError) -> Nat
         done!(Ok(file)) -> (
           wrote = file.write_all!([104, 105])
           closed = file.close!()
           1
         )
         done!(Err(_)) -> 0",
    );
    let (status, _, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!(status, 5);
    assert_eq!(left["a.txt"], b"hi");
    assert_eq!(left["b.txt"], b"hi");
}

/// A fake holding a file is lent to a generic helper that writes through
/// it, between writes to standard output, and closed once after: what it
/// wrote is in the file, in the order written.
#[test]
fn a_fake_holding_a_file_is_lent_to_a_generic_helper() {
    let package = Package::new(
        "logged",
        "import std.host {Host, File, Mode.*}

         Logged : [Logged(File)].(
           write_all! : (Logged, List(U8)) -> Result(Nat, [Lost])
           write_all!(Logged(file), bytes) -> (
             wrote = file.write_all!(bytes)
             if wrote is Ok(n) then Ok(n) else Err(Lost)
           )

           close! : Logged -> Nat
           close!(Logged(file)) -> (
             closed = file.close!()
             if closed is Ok(_) then 0 else 1
           )
         )

         say!(out, text) -> (
           wrote = out.write_all!(text.to_utf8())
           n = wrote?
           Ok(n)
         )

         main! : Host -> []
         main!(host) -> (
           opened = host.files.open!(\"log.txt\", Overwrite)
           if opened is Ok(file) then logging!(host, Logged(file)) else host.exit!(2)
         )

         logging!(host, log) -> (
           a = say!(log, \"one \")
           b = say!(host.stdout, \"two\")
           c = say!(log, \"three\")
           closed = log.close!()
           host.exit!(U8.of_nat(closed))
         )",
    );
    let (status, written, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!((status, written.as_str()), (0, "two"));
    assert_eq!(left["log.txt"], b"one three");
}

/// A name holding a nought byte is refused before the target is asked,
/// which would read it as ending there: nothing named by its front is made.
#[test]
fn a_name_holding_a_nought_byte_is_refused() {
    let package = Package::new(
        "nought-name",
        "import std.host {Host, File, IoError, Mode.*}

         main! : Host -> []
         main!(host) -> (
           opened = host.files.open!(\"bad\\0name\", Overwrite)
           status = shut!(opened)
           host.exit!(U8.of_nat(status))
         )

         shut! : Result(File, IoError) -> Nat
         shut!(Ok(file)) -> (
           closed = file.close!()
           0
         )
         shut!(Err(Other(_))) -> 6
         shut!(Err(_)) -> 7",
    );
    let (status, _, left) = support::run_among(&package.entry(), Directory::new());
    assert_eq!((status, left), (6, Directory::new()));
}
