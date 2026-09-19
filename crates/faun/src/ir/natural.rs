//! Generated, target-independent natural arithmetic on base-256 digits.
//!
//! Inputs are borrowed; every natural result owns a claim. The caller must
//! release it. Objects have three target-word headers: total block bytes,
//! reference count, and normalized digit count. Digits are little endian.
//! Static objects have an all-ones count. Mortal objects live in a private,
//! reusable, coalescing globals heap; exhaustion exits with status two.

// The generated arithmetic follows the usual a/b, i/j, carry notation.
#![allow(clippy::many_single_char_names)]

use num_bigint::BigUint;

use super::{
    Binary, Builder, Class, DataId, FunctionId, Offset, Program, Relation, Terminator, ValueId,
    Width,
};

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub word_bits: u16,
    pub heap_bytes: usize,
}

// These independent switches describe a dependency set, not runtime state.
#[expect(clippy::struct_excessive_bools)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Needs {
    pub add: bool,
    pub sub: bool,
    pub mul: bool,
    pub div: bool,
    pub modulo: bool,
    pub compare: bool,
    pub from_word: bool,
    pub to_word: bool,
}

#[derive(Clone, Debug)]
pub struct Library {
    pub zero: DataId,
    pub retain: FunctionId,
    pub release: FunctionId,
    pub add: Option<FunctionId>,
    pub sub: Option<FunctionId>,
    pub mul: Option<FunctionId>,
    pub div: Option<FunctionId>,
    pub modulo: Option<FunctionId>,
    pub compare: Option<FunctionId>,
    pub from_word: Option<FunctionId>,
    pub to_word: Option<FunctionId>,
}

const A: Class = Class::Address;
const W: Class = Class::Word;
const END: Terminator = Terminator::UNREACHABLE;

impl Config {
    fn checked(self) -> Result<(usize, u64), String> {
        if !matches!(self.word_bits, 16 | 32 | 64) {
            return Err("natural runtime needs a 16, 32, or 64 bit word".to_owned());
        }
        let bytes = usize::from(self.word_bits / 8);
        let max = u64::MAX >> (64 - self.word_bits);
        if self.heap_bytes < 4 * bytes
            || !self.heap_bytes.is_multiple_of(bytes)
            || !u64::try_from(self.heap_bytes).is_ok_and(|n| n <= max)
            || u32::try_from(self.heap_bytes).is_err()
        {
            return Err(
                "natural heap must fit a word, be word-aligned, and hold a header and digit"
                    .to_owned(),
            );
        }
        Ok((bytes, max))
    }
}

fn header(bytes: &mut [u8], at: usize, value: u64, word: usize) {
    bytes[at * word..(at + 1) * word].copy_from_slice(&value.to_le_bytes()[..word]);
}

/// Append an immortal natural in the runtime representation.
///
/// # Errors
/// If the configuration or object size does not fit the target.
pub fn constant(
    program: &mut Program,
    config: Config,
    magnitude: &BigUint,
) -> Result<DataId, String> {
    let (word, max) = config.checked()?;
    let mut digits = magnitude.to_bytes_le();
    while digits.last() == Some(&0) {
        digits.pop();
    }
    let size = digits
        .len()
        .checked_add(4 * word - 1)
        .map(|n| n / word * word)
        .ok_or_else(|| "natural constant is too large".to_owned())?;
    if !u64::try_from(size).is_ok_and(|n| n <= max) || u32::try_from(size).is_err() {
        return Err("natural constant does not fit the target address space".to_owned());
    }
    let padding = (word - program.data().len() % word) % word;
    if program
        .data()
        .len()
        .checked_add(padding)
        .and_then(|n| n.checked_add(size))
        .is_none_or(|n| u32::try_from(n).is_err())
    {
        return Err("natural constants exceed the data pool".to_owned());
    }
    if padding != 0 {
        program.intern(&vec![0; padding]);
    }
    let mut bytes = vec![0; size];
    header(&mut bytes, 0, size64(size), word);
    header(&mut bytes, 1, max, word);
    header(&mut bytes, 2, size64(digits.len()), word);
    bytes[3 * word..3 * word + digits.len()].copy_from_slice(&digits);
    Ok(program.intern(&bytes))
}

fn size64(n: usize) -> u64 {
    u64::try_from(n).expect("a checked pool size fits u64")
}

fn number(b: &mut Builder<'_>, n: u64) -> ValueId {
    b.constant(W, n)
}

fn add(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.binary(Binary::Add, a, c)
}

fn sub(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.binary(Binary::Sub, a, c)
}

fn eq(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.compare(Relation::Equal, a, c)
}

fn lt(b: &mut Builder<'_>, a: ValueId, c: ValueId) -> ValueId {
    b.compare(Relation::Less, a, c)
}

fn call(b: &mut Builder<'_>, f: FunctionId, args: &[ValueId]) -> ValueId {
    b.call(f, args)[0]
}

fn address(b: &mut Builder<'_>, base: ValueId, offset: ValueId) -> ValueId {
    let base = b.convert(W, base);
    let at = add(b, base, offset);
    b.convert(A, at)
}

fn length(b: &mut Builder<'_>, a: ValueId) -> ValueId {
    b.load(Width::Word, a, Offset::Words(2))
}

fn set_length(b: &mut Builder<'_>, a: ValueId, n: ValueId) {
    b.store(Width::Word, a, Offset::Words(2), n);
}

fn digit_address(b: &mut Builder<'_>, a: ValueId, i: ValueId, word: usize) -> ValueId {
    let header = number(b, size64(3 * word));
    let offset = add(b, i, header);
    address(b, a, offset)
}

fn read_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, word: usize) -> ValueId {
    let at = digit_address(b, a, i, word);
    b.load(Width::Byte, at, Offset::Bytes(0))
}

fn write_digit(b: &mut Builder<'_>, a: ValueId, i: ValueId, v: ValueId, word: usize) {
    let at = digit_address(b, a, i, word);
    b.store(Width::Byte, at, Offset::Bytes(0), v);
}

fn declare(p: &mut Program, name: &str, params: &[Class], result: &[Class]) -> FunctionId {
    p.declare(name, params, result)
}

/// Append only the requested arithmetic families and their dependencies.
///
/// Helper calls have at most four arguments and one result; loops carry at
/// most two values, so the library also fits the narrowest target's ABI.
///
/// # Errors
/// If the heap configuration or required exit contract is invalid.
pub fn append(program: &mut Program, config: Config, needs: Needs) -> Result<Library, String> {
    let (word, max) = config.checked()?;
    let exit = program
        .routines()
        .get("exit")
        .ok_or_else(|| "natural runtime requires exit(word)".to_owned())?;
    if exit.takes != [W] || exit.answers.is_some() || exit.comes_back {
        return Err("natural runtime requires nonreturning exit(word)".to_owned());
    }
    let zero = constant(program, config, &BigUint::default())?;
    let (retain, release, fail) = claims(program, max);
    let mut library = Library {
        zero,
        retain,
        release,
        add: None,
        sub: None,
        mul: None,
        div: None,
        modulo: None,
        compare: needs.compare.then(|| comparison(program, word)),
        from_word: None,
        to_word: needs.to_word.then(|| narrowing(program, word)),
    };
    if needs.add || needs.sub || needs.mul || needs.div || needs.modulo || needs.from_word {
        let alloc = allocator(program, config, word, zero, fail)?;
        let trim = trimming(program, word);
        let finish = finishing(program, trim, release, zero);
        let storage = Storage {
            config,
            word,
            alloc,
            trim,
            finish,
            fail,
        };
        storage.append(program, needs, &mut library);
    }
    Ok(library)
}

fn claims(program: &mut Program, max: u64) -> (FunctionId, FunctionId, FunctionId) {
    let exit = program.platform("exit");
    let fail = declare(program, "nat.fail", &[], &[]);
    program.define(fail, |b, _| {
        let status = number(b, 2);
        b.platform_call(exit, &[status]);
        END
    });
    let retain = declare(program, "nat.retain", &[A], &[A]);
    let release = declare(program, "nat.release", &[A], &[]);
    counting(program, retain, release, fail, max);
    (retain, release, fail)
}

#[derive(Clone, Copy)]
struct Storage {
    config: Config,
    word: usize,
    alloc: FunctionId,
    trim: FunctionId,
    finish: FunctionId,
    fail: FunctionId,
}

impl Storage {
    fn append(self, p: &mut Program, needs: Needs, lib: &mut Library) {
        if needs.from_word {
            lib.from_word = Some(promotion(p, self.alloc, self.finish, lib.zero, self.word));
        }
        if needs.mul {
            lib.mul = Some(multiplication(p, self, lib.zero));
        }
        if needs.add || needs.sub || needs.div || needs.modulo {
            let digit = digit_reader(p, self.word);
            if needs.add {
                lib.add = Some(addition(p, self, digit));
            }
            if needs.sub || needs.div || needs.modulo {
                self.append_subdivision(p, needs, lib, digit);
            }
        }
    }

    fn append_subdivision(
        self,
        p: &mut Program,
        needs: Needs,
        lib: &mut Library,
        digit: FunctionId,
    ) {
        let compare = lib.compare.unwrap_or_else(|| comparison(p, self.word));
        let subtract = subtracting(p, digit, self.trim, self.word);
        if needs.sub {
            lib.sub = Some(monus(p, self, compare, subtract, lib.zero));
        }
        if needs.div || needs.modulo {
            let divmod = division(p, self, compare, subtract, lib);
            lib.div = needs.div.then(|| division_entry(p, divmod, false));
            lib.modulo = needs.modulo.then(|| division_entry(p, divmod, true));
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "two symmetric generated reference-count routines"
)]
fn counting(p: &mut Program, retain: FunctionId, release: FunctionId, fail: FunctionId, max: u64) {
    p.define(retain, |b, args| {
        let a = args[0];
        let refs = b.load(Width::Word, a, Offset::Words(1));
        let immortal = number(b, max);
        let static_ = eq(b, refs, immortal);
        b.if_(
            static_,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let limit = number(b, max - 1);
                let full = eq(b, refs, limit);
                b.if_(
                    full,
                    &[],
                    |b| {
                        b.call(fail, &[]);
                        END
                    },
                    |b| b.yield_(&[]),
                );
                let one = number(b, 1);
                let next = add(b, refs, one);
                b.store(Width::Word, a, Offset::Words(1), next);
                b.yield_(&[])
            },
        );
        b.ret(&[a])
    });
    p.define(release, |b, args| {
        let a = args[0];
        let refs = b.load(Width::Word, a, Offset::Words(1));
        let immortal = number(b, max);
        let static_ = eq(b, refs, immortal);
        b.if_(
            static_,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let one = number(b, 1);
                let next = sub(b, refs, one);
                b.store(Width::Word, a, Offset::Words(1), next);
                b.yield_(&[])
            },
        );
        b.ret(&[])
    });
}

// The request checks and first-fit scan stay together; nested work is
// generated separately to bound the narrow target's frame pressure.
#[expect(clippy::too_many_lines)]
fn allocator(
    p: &mut Program,
    config: Config,
    word: usize,
    zero: DataId,
    fail: FunctionId,
) -> Result<FunctionId, String> {
    let padding = (word - p.globals().len() % word) % word;
    if p.globals()
        .len()
        .checked_add(padding)
        .and_then(|n| n.checked_add(config.heap_bytes))
        .is_none_or(|n| u32::try_from(n).is_err())
    {
        return Err("natural heap exceeds the globals pool".to_owned());
    }
    if padding != 0 {
        p.global(&vec![0; padding]);
    }
    let mut bytes = vec![0; config.heap_bytes];
    header(&mut bytes, 0, size64(config.heap_bytes), word);
    let heap = p.global(&bytes);
    let coalesce = coalescing(p);
    let claim = claiming(p, word);
    let allocate = declare(p, "nat.allocate", &[W], &[A]);
    p.define(allocate, |b, args| {
        let cap = args[0];
        let nil = number(b, 0);
        let empty = eq(b, cap, nil);
        b.if_(
            empty,
            &[],
            |b| {
                let z = b.address_of(zero);
                b.ret(&[z])
            },
            |b| b.yield_(&[]),
        );
        let limit = number(b, size64(config.heap_bytes - 3 * word));
        let huge = lt(b, limit, cap);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
                END
            },
            |b| b.yield_(&[]),
        );
        // The aligned pool fits a word, so even the rounding addition fits.
        let overhead = number(b, size64(4 * word - 1));
        let size = add(b, cap, overhead);
        let unit = number(b, size64(word));
        let units = b.binary(Binary::Div, size, unit);
        let wanted = b.binary(Binary::Mul, units, unit);
        let base = b.address_of(heap);
        let pool = number(b, size64(config.heap_bytes));
        let result = b.loop_(&[nil], &[A], |b, state| {
            let offset = state[0];
            let end = eq(b, offset, pool);
            b.if_(
                end,
                &[],
                |b| {
                    b.call(fail, &[]);
                    END
                },
                |b| b.yield_(&[]),
            );
            let at = address(b, base, offset);
            let size = b.load(Width::Word, at, Offset::Words(0));
            let refs = b.load(Width::Word, at, Offset::Words(1));
            let free = eq(b, refs, nil);
            b.if_(
                free,
                &[],
                |b| {
                    let merged = call(b, coalesce, &[base, offset, pool]);
                    b.store(Width::Word, at, Offset::Words(0), merged);
                    let small = lt(b, merged, wanted);
                    b.if_(
                        small,
                        &[],
                        |b| {
                            let next = add(b, offset, merged);
                            b.continue_(&[next])
                        },
                        |b| {
                            b.call(claim, &[at, wanted, cap]);
                            b.break_(&[at])
                        },
                    );
                    END
                },
                |b| {
                    let next = add(b, offset, size);
                    b.continue_(&[next])
                },
            );
            END
        })[0];
        b.ret(&[result])
    });
    Ok(allocate)
}

fn coalescing(p: &mut Program) -> FunctionId {
    let f = declare(p, "nat.coalesce", &[A, W, W], &[W]);
    p.define(f, |b, args| {
        let base = args[0];
        let offset = args[1];
        let pool = args[2];
        let at = address(b, base, offset);
        let size = b.load(Width::Word, at, Offset::Words(0));
        let nil = number(b, 0);
        let merged = b.loop_(&[size], &[W], |b, state| {
            let size = state[0];
            let next = add(b, offset, size);
            let end = eq(b, next, pool);
            b.if_(end, &[], |b| b.break_(&[size]), |b| b.yield_(&[]));
            let after = address(b, base, next);
            let refs = b.load(Width::Word, after, Offset::Words(1));
            let free = eq(b, refs, nil);
            b.if_(
                free,
                &[],
                |b| {
                    let more = b.load(Width::Word, after, Offset::Words(0));
                    let total = add(b, size, more);
                    b.continue_(&[total])
                },
                |b| b.break_(&[size]),
            );
            END
        })[0];
        b.ret(&[merged])
    });
    f
}

fn claiming(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.claim", &[A, W, W], &[]);
    p.define(f, |b, args| {
        let at = args[0];
        let wanted = args[1];
        let cap = args[2];
        let merged = b.load(Width::Word, at, Offset::Words(0));
        let rest = sub(b, merged, wanted);
        let minimum = number(b, size64(4 * word));
        let tiny = lt(b, rest, minimum);
        let nil = number(b, 0);
        let one = number(b, 1);
        b.if_(
            tiny,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let tail = address(b, at, wanted);
                b.store(Width::Word, tail, Offset::Words(0), rest);
                b.store(Width::Word, tail, Offset::Words(1), nil);
                b.store(Width::Word, tail, Offset::Words(2), nil);
                b.store(Width::Word, at, Offset::Words(0), wanted);
                b.yield_(&[])
            },
        );
        b.store(Width::Word, at, Offset::Words(1), one);
        set_length(b, at, cap);
        b.loop_(&[nil], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, cap);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            write_digit(b, at, i, nil, word);
            let next = add(b, i, one);
            b.continue_(&[next])
        });
        b.ret(&[])
    });
    f
}

fn digit_reader(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.digit", &[A, W], &[W]);
    p.define(f, |b, args| {
        let len = length(b, args[0]);
        let inside = lt(b, args[1], len);
        let value = b.if_(
            inside,
            &[W],
            |b| {
                let digit = read_digit(b, args[0], args[1], word);
                b.yield_(&[digit])
            },
            |b| {
                let zero = number(b, 0);
                b.yield_(&[zero])
            },
        )[0];
        b.ret(&[value])
    });
    f
}

fn trimming(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.trim", &[A], &[]);
    p.define(f, |b, args| {
        let a = args[0];
        let len = length(b, a);
        let zero = number(b, 0);
        let one = number(b, 1);
        let n = b.loop_(&[len], &[W], |b, state| {
            let n = state[0];
            let empty = eq(b, n, zero);
            b.if_(empty, &[], |b| b.break_(&[n]), |b| b.yield_(&[]));
            let last = sub(b, n, one);
            let digit = read_digit(b, a, last, word);
            let empty = eq(b, digit, zero);
            b.if_(empty, &[], |b| b.continue_(&[last]), |b| b.break_(&[n]));
            END
        })[0];
        set_length(b, a, n);
        b.ret(&[])
    });
    f
}

fn finishing(p: &mut Program, trim: FunctionId, release: FunctionId, zero: DataId) -> FunctionId {
    let f = declare(p, "nat.finish", &[A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        b.call(trim, &[a]);
        let len = length(b, a);
        let nil = number(b, 0);
        let empty = eq(b, len, nil);
        let value = b.if_(
            empty,
            &[A],
            |b| {
                b.call(release, &[a]);
                let z = b.address_of(zero);
                b.yield_(&[z])
            },
            |b| b.yield_(&[a]),
        )[0];
        b.ret(&[value])
    });
    f
}

fn comparison(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.compare", &[A, A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let zero = number(b, 0);
        let one = number(b, 1);
        let two = number(b, 2);
        let less = lt(b, la, lc);
        b.if_(less, &[], |b| b.ret(&[zero]), |b| b.yield_(&[]));
        let greater = lt(b, lc, la);
        b.if_(greater, &[], |b| b.ret(&[two]), |b| b.yield_(&[]));
        let order = b.loop_(&[la], &[W], |b, state| {
            let n = state[0];
            let empty = eq(b, n, zero);
            b.if_(empty, &[], |b| b.break_(&[one]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let x = read_digit(b, a, i, word);
            let y = read_digit(b, c, i, word);
            let less = lt(b, x, y);
            b.if_(less, &[], |b| b.break_(&[zero]), |b| b.yield_(&[]));
            let greater = lt(b, y, x);
            b.if_(greater, &[], |b| b.break_(&[two]), |b| b.continue_(&[i]));
            END
        })[0];
        b.ret(&[order])
    });
    f
}

#[expect(
    clippy::too_many_lines,
    reason = "one generated carry-propagation routine"
)]
fn addition(p: &mut Program, storage: Storage, digit: FunctionId) -> FunctionId {
    let Storage {
        alloc,
        finish,
        fail,
        config,
        word,
        ..
    } = storage;
    let f = declare(p, "nat.add", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let less = lt(b, la, lc);
        let len = b.if_(less, &[W], |b| b.yield_(&[lc]), |b| b.yield_(&[la]))[0];
        let limit = number(b, size64(config.heap_bytes - 3 * word));
        let fits = lt(b, len, limit);
        b.if_(
            fits,
            &[],
            |b| b.yield_(&[]),
            |b| {
                b.call(fail, &[]);
                END
            },
        );
        let one = number(b, 1);
        let zero = number(b, 0);
        let radix = number(b, 256);
        let cap = add(b, len, one);
        let out = call(b, alloc, &[cap]);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let i = state[0];
            let carry = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = call(b, digit, &[a, i]);
            let y = call(b, digit, &[c, i]);
            let sum = add(b, x, y);
            let sum = add(b, sum, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high])
        })[0];
        write_digit(b, out, len, carry, word);
        let result = call(b, finish, &[out]);
        b.ret(&[result])
    });
    f
}

// Mutates a unique scratch object, known >= the borrowed right operand.
fn subtracting(p: &mut Program, digit: FunctionId, trim: FunctionId, word: usize) -> FunctionId {
    let f = declare(p, "nat.subtract_into", &[A, A], &[]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let len = length(b, a);
        let zero = number(b, 0);
        let one = number(b, 1);
        let radix = number(b, 256);
        b.loop_(&[zero, zero], &[], |b, state| {
            let i = state[0];
            let borrow = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, a, i, word);
            let y = call(b, digit, &[c, i]);
            let y = add(b, y, borrow);
            let borrow = lt(b, x, y);
            let low = b.if_(
                borrow,
                &[W],
                |b| {
                    let wide = add(b, x, radix);
                    let low = sub(b, wide, y);
                    b.yield_(&[low])
                },
                |b| {
                    let low = sub(b, x, y);
                    b.yield_(&[low])
                },
            )[0];
            write_digit(b, a, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, borrow])
        });
        b.call(trim, &[a]);
        b.ret(&[])
    });
    f
}

fn monus(
    p: &mut Program,
    storage: Storage,
    compare: FunctionId,
    subtract: FunctionId,
    zero: DataId,
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        ..
    } = storage;
    let f = declare(p, "nat.sub", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let order = call(b, compare, &[a, c]);
        let two = number(b, 2);
        let greater = eq(b, order, two);
        b.if_(
            greater,
            &[],
            |b| b.yield_(&[]),
            |b| {
                let z = b.address_of(zero);
                b.ret(&[z])
            },
        );
        let len = length(b, a);
        let out = call(b, alloc, &[len]);
        let zero = number(b, 0);
        let one = number(b, 1);
        b.loop_(&[zero], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let x = read_digit(b, a, i, word);
            write_digit(b, out, i, x, word);
            let next = add(b, i, one);
            b.continue_(&[next])
        });
        b.call(subtract, &[out, c]);
        let result = call(b, finish, &[out]);
        b.ret(&[result])
    });
    f
}

fn multiply_row(p: &mut Program, word: usize) -> FunctionId {
    let row = declare(p, "nat.multiply_row", &[A, A, A, W], &[]);
    p.define(row, |b, args| {
        let a = args[0];
        let c = args[1];
        let out = args[2];
        let i = args[3];
        let x = read_digit(b, a, i, word);
        let len = length(b, c);
        let zero = number(b, 0);
        let one = number(b, 1);
        let radix = number(b, 256);
        let carry = b.loop_(&[zero, zero], &[W], |b, state| {
            let j = state[0];
            let carry = state[1];
            let done = eq(b, j, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let y = read_digit(b, c, j, word);
            let at = add(b, i, j);
            let acc = read_digit(b, out, at, word);
            // 255*255 + 255 + 255 = 65535, even on a 16-bit target.
            let product = b.binary(Binary::Mul, x, y);
            let sum = add(b, product, acc);
            let sum = add(b, sum, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, at, low, word);
            let next = add(b, j, one);
            b.continue_(&[next, high])
        })[0];
        let at = add(b, i, len);
        write_digit(b, out, at, carry, word);
        b.ret(&[])
    });
    row
}

#[expect(
    clippy::too_many_lines,
    reason = "checks and generated outer product loop"
)]
fn multiplication(p: &mut Program, storage: Storage, zero: DataId) -> FunctionId {
    let Storage {
        alloc,
        finish,
        fail,
        config,
        word,
        ..
    } = storage;
    let row = multiply_row(p, word);
    let f = declare(p, "nat.mul", &[A, A], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let la = length(b, a);
        let lc = length(b, c);
        let nil = number(b, 0);
        let one = number(b, 1);
        for len in [la, lc] {
            let empty = eq(b, len, nil);
            b.if_(
                empty,
                &[],
                |b| {
                    let z = b.address_of(zero);
                    b.ret(&[z])
                },
                |b| b.yield_(&[]),
            );
        }
        // Check each component before addition, including large static inputs.
        let limit = number(b, size64(config.heap_bytes - 3 * word));
        let huge = lt(b, limit, la);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
                END
            },
            |b| b.yield_(&[]),
        );
        let room = sub(b, limit, la);
        let huge = lt(b, room, lc);
        b.if_(
            huge,
            &[],
            |b| {
                b.call(fail, &[]);
                END
            },
            |b| b.yield_(&[]),
        );
        let cap = add(b, la, lc);
        let out = call(b, alloc, &[cap]);
        b.loop_(&[nil], &[], |b, state| {
            let i = state[0];
            let done = eq(b, i, la);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            b.call(row, &[a, c, out, i]);
            let next = add(b, i, one);
            b.continue_(&[next])
        });
        let result = call(b, finish, &[out]);
        b.ret(&[result])
    });
    f
}

// r <- 2*r+bit, in a unique remainder with one spare digit.
fn shifting(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.shift_in", &[A, W], &[]);
    p.define(f, |b, args| {
        let out = args[0];
        let bit = args[1];
        let len = length(b, out);
        let zero = number(b, 0);
        let one = number(b, 1);
        let two = number(b, 2);
        let radix = number(b, 256);
        let carry = b.loop_(&[zero, bit], &[W], |b, state| {
            let i = state[0];
            let carry = state[1];
            let done = eq(b, i, len);
            b.if_(done, &[], |b| b.break_(&[carry]), |b| b.yield_(&[]));
            let x = read_digit(b, out, i, word);
            let doubled = b.binary(Binary::Mul, x, two);
            let sum = add(b, doubled, carry);
            let low = b.binary(Binary::Mod, sum, radix);
            let high = b.binary(Binary::Div, sum, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high])
        })[0];
        let empty = eq(b, carry, zero);
        b.if_(
            empty,
            &[],
            |b| b.yield_(&[]),
            |b| {
                write_digit(b, out, len, carry, word);
                let next = add(b, len, one);
                set_length(b, out, next);
                b.yield_(&[])
            },
        );
        b.ret(&[])
    });
    f
}

fn divide_digit(
    p: &mut Program,
    compare: FunctionId,
    subtract: FunctionId,
    word: usize,
) -> FunctionId {
    let shift = shifting(p, word);
    // This one-byte quotient step keeps the division's outer loop small.
    let step = declare(p, "nat.divide_digit", &[A, A, W], &[W]);
    p.define(step, |b, args| {
        let r = args[0];
        let divisor = args[1];
        let digit = args[2];
        let zero = number(b, 0);
        let two = number(b, 2);
        let top = number(b, 128);
        let answer = b.loop_(&[top, zero], &[W], |b, state| {
            let mask = state[0];
            let quotient = state[1];
            let done = eq(b, mask, zero);
            b.if_(done, &[], |b| b.break_(&[quotient]), |b| b.yield_(&[]));
            let part = b.binary(Binary::Div, digit, mask);
            let bit = b.binary(Binary::Mod, part, two);
            b.call(shift, &[r, bit]);
            let order = call(b, compare, &[r, divisor]);
            let less = eq(b, order, zero);
            let quotient = b.if_(
                less,
                &[W],
                |b| b.yield_(&[quotient]),
                |b| {
                    b.call(subtract, &[r, divisor]);
                    let next = add(b, quotient, mask);
                    b.yield_(&[next])
                },
            )[0];
            let next = b.binary(Binary::Div, mask, two);
            b.continue_(&[next, quotient])
        })[0];
        b.ret(&[answer])
    });
    step
}

#[expect(
    clippy::too_many_lines,
    reason = "one generated div/mod routine and its scratch lifetimes"
)]
fn division(
    p: &mut Program,
    storage: Storage,
    compare: FunctionId,
    subtract: FunctionId,
    lib: &Library,
) -> FunctionId {
    let Storage {
        alloc,
        finish,
        word,
        ..
    } = storage;
    let Library {
        retain,
        release,
        zero,
        ..
    } = *lib;
    let step = divide_digit(p, compare, subtract, word);
    let f = declare(p, "nat.divmod", &[A, A, W], &[A]);
    p.define(f, |b, args| {
        let a = args[0];
        let c = args[1];
        let remainder = args[2];
        let la = length(b, a);
        let lc = length(b, c);
        let nil = number(b, 0);
        let one = number(b, 1);
        let empty = eq(b, lc, nil);
        let order = call(b, compare, &[a, c]);
        let less = eq(b, order, nil);
        // Both trivial paths borrow `a` and must create an owned result.
        for trivial in [empty, less] {
            b.if_(
                trivial,
                &[],
                |b| {
                    let answer = b.if_(
                        remainder,
                        &[A],
                        |b| {
                            let kept = call(b, retain, &[a]);
                            b.yield_(&[kept])
                        },
                        |b| {
                            let z = b.address_of(zero);
                            b.yield_(&[z])
                        },
                    )[0];
                    b.ret(&[answer])
                },
                |b| b.yield_(&[]),
            );
        }
        // lc+1 cannot overflow: a valid object also has its three-word header.
        let cap = add(b, lc, one);
        let r = call(b, alloc, &[cap]);
        set_length(b, r, nil);
        let q = call(b, alloc, &[la]);
        b.loop_(&[la], &[], |b, state| {
            let n = state[0];
            let done = eq(b, n, nil);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let digit = read_digit(b, a, i, word);
            let quotient = call(b, step, &[r, c, digit]);
            write_digit(b, q, i, quotient, word);
            b.continue_(&[i])
        });
        let out = b.if_(
            remainder,
            &[A],
            |b| {
                b.call(release, &[q]);
                let out = call(b, finish, &[r]);
                b.yield_(&[out])
            },
            |b| {
                b.call(release, &[r]);
                let out = call(b, finish, &[q]);
                b.yield_(&[out])
            },
        )[0];
        b.ret(&[out])
    });
    f
}

fn division_entry(p: &mut Program, divmod: FunctionId, remainder: bool) -> FunctionId {
    let name = if remainder { "nat.mod" } else { "nat.div" };
    let f = declare(p, name, &[A, A], &[A]);
    p.define(f, |b, args| {
        let mode = number(b, u64::from(remainder));
        let out = call(b, divmod, &[args[0], args[1], mode]);
        b.ret(&[out])
    });
    f
}

fn promotion(
    p: &mut Program,
    alloc: FunctionId,
    finish: FunctionId,
    zero: DataId,
    word: usize,
) -> FunctionId {
    let f = declare(p, "nat.from_word", &[W], &[A]);
    p.define(f, |b, args| {
        let value = args[0];
        let nil = number(b, 0);
        let empty = eq(b, value, nil);
        b.if_(
            empty,
            &[],
            |b| {
                let z = b.address_of(zero);
                b.ret(&[z])
            },
            |b| b.yield_(&[]),
        );
        let cap = number(b, size64(word));
        let out = call(b, alloc, &[cap]);
        let radix = number(b, 256);
        let one = number(b, 1);
        b.loop_(&[nil, value], &[], |b, state| {
            let i = state[0];
            let n = state[1];
            let done = eq(b, i, cap);
            b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
            let low = b.binary(Binary::Mod, n, radix);
            let high = b.binary(Binary::Div, n, radix);
            write_digit(b, out, i, low, word);
            let next = add(b, i, one);
            b.continue_(&[next, high])
        });
        let result = call(b, finish, &[out]);
        b.ret(&[result])
    });
    f
}

fn narrowing(p: &mut Program, word: usize) -> FunctionId {
    let f = declare(p, "nat.to_word", &[A], &[W]);
    p.define(f, |b, args| {
        let a = args[0];
        let len = length(b, a);
        let max = number(b, size64(word));
        let less = lt(b, len, max);
        let count = b.if_(less, &[W], |b| b.yield_(&[len]), |b| b.yield_(&[max]))[0];
        let zero = number(b, 0);
        let one = number(b, 1);
        let radix = number(b, 256);
        let out = b.loop_(&[count, zero], &[W], |b, state| {
            let n = state[0];
            let value = state[1];
            let done = eq(b, n, zero);
            b.if_(done, &[], |b| b.break_(&[value]), |b| b.yield_(&[]));
            let i = sub(b, n, one);
            let digit = read_digit(b, a, i, word);
            let high = b.binary(Binary::Mul, value, radix);
            let value = add(b, high, digit);
            b.continue_(&[i, value])
        })[0];
        b.ret(&[out])
    });
    f
}
