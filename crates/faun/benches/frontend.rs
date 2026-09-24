use std::hint::black_box;
use std::time::{Duration, Instant};

const LINES: usize = 100_000;
const LINES_AS_F64: f64 = 100_000.0;
const GOAL: f64 = 500_000.0;
const RUNS: usize = 7;

fn main() {
    let clauses = "id(x) -> x\n".repeat(LINES);
    let mixed_block = concat!(
        "Tree(a) : [Leaf(a) Branch(Tree(a) Tree(a))]\n",
        "size : Tree(Nat) -> Nat\n",
        "size(Leaf(_)) -> 1\n",
        "size(Branch(left right)) -> size(left) + size(right) + 1\n",
        "compute(value) -> next = value.step(1) next * 2 + 3\n",
    );
    let mixed = mixed_block.repeat(LINES / 5);
    let constructors = "build(x) -> Succ(Succ(Succ(Succ(Succ(Succ(x))))))\n".repeat(LINES);

    benchmark("clauses", &clauses);
    benchmark("mixed", &mixed);
    benchmark("ctors", &constructors);
}

fn benchmark(name: &str, source: &str) {
    let tokens = faun::lex::lex(black_box(source)).expect("benchmark source lexes");
    black_box(tokens);
    let module = faun::parse(black_box(source)).expect("benchmark source parses");
    assert_eq!(module.items.len(), LINES);
    black_box(module);

    let lex = best_of(|| {
        let tokens = faun::lex::lex(black_box(source)).expect("benchmark source lexes");
        black_box(tokens);
    });
    let parse = best_of(|| {
        let module = faun::parse(black_box(source)).expect("benchmark source parses");
        black_box(module);
    });

    print_rate(name, "lex", source.len(), lex);
    print_rate(name, "lex + parse", source.len(), parse);
}

fn best_of(mut run: impl FnMut()) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..RUNS {
        let started = Instant::now();
        run();
        best = best.min(started.elapsed());
    }
    best
}

fn print_rate(name: &str, stage: &str, bytes: usize, elapsed: Duration) {
    let lines_per_second = LINES_AS_F64 / elapsed.as_secs_f64();
    let mib_per_second = bytes_to_f64(bytes) / elapsed.as_secs_f64() / (1024.0 * 1024.0);
    println!(
        "{name:7} {stage:11}: {lines_per_second:>9.0} lines/s, \
         {mib_per_second:>6.1} MiB/s ({:.3}s; goal {GOAL:.0} lines/s)",
        elapsed.as_secs_f64()
    );
}

fn bytes_to_f64(bytes: usize) -> f64 {
    f64::from(u32::try_from(bytes).expect("benchmark input is smaller than 4 GiB"))
}
