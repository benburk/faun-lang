use super::shared::status;
use crate::ir::{Binary, Builder, Class, Offset, Program, Relation, ValueId, Width};
use crate::machine::{Allocated, AllocatedBuilder, Inst, MemoryWidth, Reg, RegisterWidth};
use faun_core::codegen::FrameSlot;
use faun_core::float::{Float, Format, Operation};

const XMMS: [Reg; 16] = [
    Reg::Xmm0,
    Reg::Xmm1,
    Reg::Xmm2,
    Reg::Xmm3,
    Reg::Xmm4,
    Reg::Xmm5,
    Reg::Xmm6,
    Reg::Xmm7,
    Reg::Xmm8,
    Reg::Xmm9,
    Reg::Xmm10,
    Reg::Xmm11,
    Reg::Xmm12,
    Reg::Xmm13,
    Reg::Xmm14,
    Reg::Xmm15,
];

fn equal_pattern(b: &mut Builder, value: ValueId, expected: u64, format: Format) -> ValueId {
    let value = b.convert(Class::Word, value);
    let (exponent, fraction) = match format {
        Format::Binary32 => (0x7F80_0000, 0x007F_FFFF),
        Format::Binary64 => (0x7FF0_0000_0000_0000, 0x000F_FFFF_FFFF_FFFF),
    };
    if expected & exponent == exponent && expected & fraction != 0 {
        // IEEE arithmetic does not promise a particular NaN payload. Moves
        // and spills, tested separately below, must preserve every bit.
        let exponent = b.constant(Class::Word, exponent);
        let fraction = b.constant(Class::Word, fraction);
        let e = b.binary(Binary::And, value, exponent);
        let f = b.binary(Binary::And, value, fraction);
        let zero = b.constant(Class::Word, 0);
        let e = b.compare(Relation::Equal, e, exponent);
        let f = b.compare(Relation::Less, zero, f);
        b.binary(Binary::And, e, f)
    } else {
        let expected = b.constant(Class::Word, expected);
        b.compare(Relation::Equal, value, expected)
    }
}

fn scalar_patterns(format: Format) -> &'static [u64] {
    match format {
        Format::Binary32 => &[
            0,
            0x8000_0000,
            1,
            0x3F80_0000,
            0x3F80_0001,
            0xC040_0000,
            0x7F7F_FFFF,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_1234,
            0x7FA0_5678,
        ],
        Format::Binary64 => &[
            0,
            0x8000_0000_0000_0000,
            1,
            0x3FF0_0000_0000_0000,
            0x3FF0_0000_0000_0001,
            0xC008_0000_0000_0000,
            0x7FEF_FFFF_FFFF_FFFF,
            0x7FF0_0000_0000_0000,
            0xFFF0_0000_0000_0000,
            0x7FF8_0000_0000_1234,
            0x7FF0_0000_0000_5678,
        ],
    }
}

#[test]
fn scalar_arithmetic_preserves_rounding_signed_zero_and_operand_order() {
    for format in [Format::Binary32, Format::Binary64] {
        let patterns = scalar_patterns(format);
        let (mut program, main) = Program::new("float matrix");
        program.define(main, |b, _| {
            let mut passed = b.constant(Class::Word, 0);
            let mut cases = 0;
            for operation in [
                Operation::Add,
                Operation::Sub,
                Operation::Mul,
                Operation::Div,
                Operation::Sqrt,
            ] {
                let float = Float { format, operation };
                for &left in patterns {
                    for &right in if operation == Operation::Sqrt {
                        &patterns[..1]
                    } else {
                        patterns
                    } {
                        let bits = &[left, right][..operation.arity()];
                        let args: Vec<_> = bits
                            .iter()
                            .map(|&bits| b.constant(Class::fixed(format.bits()), bits))
                            .collect();
                        let value = b.float(float, &args);
                        let equal = equal_pattern(b, value, float.calculate(bits), format);
                        passed = b.binary(Binary::Add, passed, equal);
                        cases += 1;
                    }
                }
            }
            let cases = b.constant(Class::Word, cases);
            let failed = b.compare(Relation::Less, passed, cases);
            b.ret(&[failed]);
        });
        assert_eq!(status(&program), 0, "{format:?}");
    }
}

#[test]
fn doubling_by_addition_matches_multiplication_in_either_order() {
    for format in [Format::Binary32, Format::Binary64] {
        let mul = Float {
            format,
            operation: Operation::Mul,
        };
        let two = match format {
            Format::Binary32 => u64::from(2.0f32.to_bits()),
            Format::Binary64 => 2.0f64.to_bits(),
        };
        let class = Class::fixed(format.bits());
        let (mut program, main) = Program::new("doubling");
        let twice = program.declare("twice", &[class], &[class, class]);
        program.define(twice, |b, args| {
            let two = b.constant(class, two);
            let left = b.float(mul, &[two, args[0]]);
            let right = b.float(mul, &[args[0], two]);
            b.ret(&[left, right]);
        });
        program.define(main, |b, _| {
            let mut passed = b.constant(Class::Word, 1);
            for &bits in scalar_patterns(format) {
                let input = b.constant(class, bits);
                for result in b.call(twice, &[input]) {
                    let equal = equal_pattern(b, result, mul.calculate(&[two, bits]), format);
                    passed = b.binary(Binary::And, passed, equal);
                }
            }
            b.ret(&[passed]);
        });
        let optimized = crate::ir::optimize(&program);
        let body = optimized.function(twice).body().unwrap();
        assert!(
            !optimized
                .every(body)
                .any(|op| matches!(op, crate::ir::Op::Float { float, .. } if *float == mul))
        );
        assert_eq!(status(&optimized), 1, "{format:?}");
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "floats live across a clobbering call, stack ABI, spill pressure and memory observations"
)]
fn float_pressure_calls_and_stack_results_preserve_every_bit() {
    let (mut program, main) = Program::new("float spills");
    let buffer = program.global(&[0; 32 * 8]);
    let source = program.intern(
        &(1..=32u32)
            .flat_map(|n| f64::from(n * n).to_bits().to_le_bytes())
            .collect::<Vec<_>>(),
    );
    let worker = program.declare(
        "sqrt many",
        &[Class::fixed(64); 32],
        &[Class::fixed(64); 32],
    );
    program.define(worker, |b, args| {
        let answers: Vec<_> = args
            .iter()
            .map(|&arg| {
                b.float(
                    Float {
                        format: Format::Binary64,
                        operation: Operation::Sqrt,
                    },
                    &[arg],
                )
            })
            .collect();
        b.ret(&answers);
    });
    program.define(main, |b, _| {
        let input = b.address_of(source);
        let output = b.address_of(buffer);
        let values: Vec<_> = (0..32)
            .map(|at| {
                let value = b.load(Width::Word, input, Offset::Bytes(at * 8));
                b.convert(Class::fixed(64), value)
            })
            .collect();
        let roots = b.call(worker, &values);
        // All 32 results must remain live through a second call whose
        // arithmetic overwrites every XMM register available to it.
        let again = b.call(worker, &values);
        for (at, &value) in roots.iter().enumerate() {
            b.store(
                Width::Word,
                output,
                Offset::Bytes(i32::try_from(at).unwrap() * 8),
                value,
            );
        }
        let mut passed = b.constant(Class::Word, 0);
        for at in 0..32i32 {
            let value = b.load(Width::Word, output, Offset::Bytes(at * 8));
            let expected = f64::from(at + 1).to_bits();
            for value in [value, again[usize::try_from(at).unwrap()]] {
                let equal = equal_pattern(b, value, expected, Format::Binary64);
                passed = b.binary(Binary::Add, passed, equal);
            }
        }
        let expected = b.constant(Class::Word, 64);
        let failed = b.binary(Binary::Sub, expected, passed);
        b.ret(&[failed]);
    });
    let allocated = crate::selected::select_and_allocate(&program).unwrap();
    assert!(allocated.instructions().iter().any(|inst| matches!(
        inst,
        Inst::Float {
            dst: Reg::Xmm15,
            ..
        }
    )));
    assert!(
        allocated
            .instructions()
            .iter()
            .any(|inst| matches!(inst, Inst::StoreFrame { src, .. } if src.is_xmm()))
    );
    assert!(
        allocated
            .instructions()
            .iter()
            .any(|inst| matches!(inst, Inst::LoadFrame { dst, .. } if dst.is_xmm()))
    );
    assert!(
        allocated
            .instructions()
            .iter()
            .any(|inst| matches!(inst, Inst::Load { dst, .. } if dst.is_xmm()))
    );
    assert_eq!(status(&program), 0);
}

#[test]
fn float_loops_joins_and_repeated_operands_keep_live_inputs() {
    let (mut program, main) = Program::new("float loop");
    program.define(main, |b, _| {
        let three = b.constant(Class::fixed(64), 3.0f64.to_bits());
        let five = b.constant(Class::fixed(64), 5.0f64.to_bits());
        let count = b.constant(Class::Word, 9);
        let result = b.loop_(&[count, three, five], &[Class::fixed(64); 2], |b, args| {
            let zero = b.constant(Class::Word, 0);
            let done = b.compare(Relation::Equal, args[0], zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&args[1..]),
                |b| {
                    let sub = Float {
                        format: Format::Binary64,
                        operation: Operation::Sub,
                    };
                    let zero = b.float(sub, &[args[1], args[1]]);
                    let add = Float {
                        operation: Operation::Add,
                        ..sub
                    };
                    let left = b.float(add, &[args[1], zero]);
                    let right = b.float(add, &[args[2], zero]);
                    let one = b.constant(Class::Word, 1);
                    let count = b.binary(Binary::Sub, args[0], one);
                    b.continue_(&[count, right, left]);
                },
            );
        });
        let left = equal_pattern(b, result[0], 5.0f64.to_bits(), Format::Binary64);
        let right = equal_pattern(b, result[1], 3.0f64.to_bits(), Format::Binary64);
        let good = b.binary(Binary::And, left, right);
        let one = b.constant(Class::fixed(1), 1);
        let bad = b.binary(Binary::Xor, good, one);
        b.ret(&[bad]);
    });
    assert_eq!(status(&program), 0);
}

#[test]
fn binary32_stores_write_four_bytes_from_the_float_bank() {
    let (mut program, main) = Program::new("float store");
    let memory = program.global(&[0xA5; 8]);
    program.define(main, |b, _| {
        let address = b.address_of(memory);
        let input = b.constant(Class::fixed(32), u64::from(9.0f32.to_bits()));
        let root = b.float(
            Float {
                format: Format::Binary32,
                operation: Operation::Sqrt,
            },
            &[input],
        );
        b.store(Width::Bits32, address, Offset::Bytes(0), root);
        let stored = b.load(Width::Word, address, Offset::Bytes(0));
        let expected = b.constant(Class::Word, 0xA5A5_A5A5_4040_0000);
        let good = b.compare(Relation::Equal, stored, expected);
        let one = b.constant(Class::fixed(1), 1);
        let bad = b.binary(Binary::Xor, good, one);
        b.ret(&[bad]);
    });
    let allocated = crate::selected::select_and_allocate(&program).unwrap();
    assert!(allocated.instructions().iter().any(
        |inst| matches!(inst, Inst::Store { width: MemoryWidth::Bits32, src, .. } if src.is_xmm())
    ));
    assert_eq!(status(&program), 0);
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "exercise every physical register encoding and bit-preserving transfer width"
)]
fn all_register_encodings_preserve_patterns_and_narrow_copies_zero_extend() {
    let mut b = AllocatedBuilder::default();
    let gprs = [
        Reg::Rax,
        Reg::Rcx,
        Reg::Rdx,
        Reg::Rbx,
        Reg::Rbp,
        Reg::Rsi,
        Reg::Rdi,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
        Reg::R12,
        Reg::R13,
        Reg::R14,
        Reg::R15,
    ];
    let slots = 16 * 15 * 5;
    b.open_frame(slots);
    let mut expected = Vec::new();
    for (at, fp) in XMMS.into_iter().enumerate() {
        for gp in gprs {
            let pattern =
                0xFFF8_1234_8000_0000 | u64::from(u8::from(fp)) << 8 | u64::from(u8::from(gp));
            let slot = u32::try_from(expected.len()).unwrap();
            b.mov_imm64(gp, pattern);
            b.mov_reg(fp, gp, RegisterWidth::Word);
            b.mov_reg(gp, fp, RegisterWidth::Word);
            b.store_slot(gp, FrameSlot::at(slot));
            b.store_slot(fp, FrameSlot::at(slot + 1));
            b.load_slot(fp, FrameSlot::at(slot + 1));
            b.mov_reg(gp, fp, RegisterWidth::Low32);
            b.store_slot(gp, FrameSlot::at(slot + 2));
            b.mov_reg(XMMS[(at + 1) % 16], fp, RegisterWidth::Low32);
            b.store_slot(XMMS[(at + 1) % 16], FrameSlot::at(slot + 3));
            b.mov_imm64(gp, pattern);
            b.mov_reg(fp, gp, RegisterWidth::Low32);
            b.store_slot(fp, FrameSlot::at(slot + 4));
            expected.extend([
                pattern,
                pattern,
                pattern & 0xFFFF_FFFF,
                pattern & 0xFFFF_FFFF,
                pattern & 0xFFFF_FFFF,
            ]);
        }
    }
    assert_eq!(
        capture(b, slots),
        expected
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>()
    );
}

#[test]
fn binary32_sqrt_clears_a_dirty_destination_and_preserves_its_source() {
    let mut b = AllocatedBuilder::default();
    b.open_frame(16 * 16 * 2);
    let mut slot = 0;
    let mut expected = Vec::new();
    for dst in XMMS {
        for src in XMMS {
            b.mov_imm64(Reg::Rax, u64::MAX);
            b.mov_reg(dst, Reg::Rax, RegisterWidth::Word);
            b.mov_imm32(Reg::Rax, 9.0f32.to_bits());
            b.mov_reg(src, Reg::Rax, RegisterWidth::Low32);
            b.float(
                Float {
                    format: Format::Binary32,
                    operation: Operation::Sqrt,
                },
                dst,
                src,
                None,
            );
            b.store_slot(dst, FrameSlot::at(slot));
            b.store_slot(src, FrameSlot::at(slot + 1));
            expected.extend([
                u64::from(3.0f32.to_bits()),
                u64::from(if dst == src { 3.0f32 } else { 9.0f32 }.to_bits()),
            ]);
            slot += 2;
        }
    }
    assert_eq!(
        capture(b, slot),
        expected
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>()
    );
}

fn capture(mut b: AllocatedBuilder, slots: u32) -> Vec<u8> {
    b.mov_imm32(Reg::Rax, 1);
    b.mov_imm32(Reg::Rdi, 1);
    b.mov_reg(Reg::Rsi, Reg::Rsp, RegisterWidth::Word);
    b.mov_imm32(Reg::Rdx, slots * 8);
    b.syscall();
    b.mov_imm32(Reg::Rax, 60);
    b.mov_imm32(Reg::Rdi, 0);
    b.syscall();
    execute(&b.finish().unwrap())
}

fn execute(program: &Allocated) -> Vec<u8> {
    use faun_core::targets::write_image;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "faun-xmm-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let image = crate::elf::image(
        &crate::encode::encode(program),
        &Program::default(),
        faun_core::targets::SymbolTable::Omitted,
    );
    write_image(&path, "", &image, true).unwrap();
    let mut command = std::process::Command::new(&path);
    let mut output = command.output();
    // A concurrent fork can briefly inherit the executable's writable fd.
    for _ in 0..64 {
        if !output
            .as_ref()
            .is_err_and(|error| error.kind() == std::io::ErrorKind::ExecutableFileBusy)
        {
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
        output = command.output();
    }
    std::fs::remove_file(path).unwrap();
    let output = output.unwrap();
    assert!(output.status.success(), "{:?}", output.status);
    output.stdout
}

#[test]
fn xmm_memory_accesses_and_self_narrowing_preserve_scalar_widths() {
    let mut b = AllocatedBuilder::default();
    b.open_frame(16 * 4);
    b.mov_reg(Reg::R12, Reg::Rsp, RegisterWidth::Word);
    let mut expected = Vec::new();
    for (at, fp) in XMMS.into_iter().enumerate() {
        let slot = u32::try_from(at).unwrap() * 4;
        let displacement = i32::try_from(slot * 8).unwrap();
        b.mov_imm64(Reg::Rax, 0xFEED_C0DE_4110_0000);
        b.store_slot(Reg::Rax, FrameSlot::at(slot));
        b.load(MemoryWidth::Bits32, fp, Reg::R12, displacement);
        b.store_slot(fp, FrameSlot::at(slot + 1));
        b.float(
            Float {
                format: Format::Binary32,
                operation: Operation::Sqrt,
            },
            fp,
            fp,
            None,
        );
        b.store(MemoryWidth::Bits32, fp, Reg::R12, displacement);
        b.load(MemoryWidth::Word, fp, Reg::R12, displacement);
        b.store_slot(fp, FrameSlot::at(slot + 2));
        b.mov_reg(fp, fp, RegisterWidth::Low32);
        b.store_slot(fp, FrameSlot::at(slot + 3));
        expected.extend([
            0xFEED_C0DE_4040_0000u64,
            0x4110_0000,
            0xFEED_C0DE_4040_0000,
            0x4040_0000,
        ]);
    }
    assert_eq!(
        capture(b, 64),
        expected
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>()
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one simultaneous cycle across both banks and two spill slots"
)]
fn mixed_bank_and_memory_copy_cycles_preserve_nan_payloads() {
    use crate::parallel_copy::{Copy, CopySource, Place, plan, temporary};
    let mut b = AllocatedBuilder::default();
    b.open_frame(6);
    let places = [
        Place::Register(Reg::Rax),
        Place::Register(Reg::Xmm15),
        Place::Frame(FrameSlot::at(2)),
        Place::Frame(FrameSlot::at(3)),
        Place::Register(Reg::R12),
        Place::Register(Reg::Xmm8),
    ];
    let patterns = [
        0x7FF8_0000_0000_1234,
        0xFFF0_0000_0000_5678,
        0x8000_0000_0000_0000,
        0x0000_0000_FFC0_1234,
        u64::MAX,
        1,
    ];
    for (place, pattern) in places.into_iter().zip(patterns) {
        b.mov_imm64(Reg::R10, pattern);
        match place {
            Place::Register(reg) => b.mov_reg(reg, Reg::R10, RegisterWidth::Word),
            Place::Frame(slot) => b.store_slot(Reg::R10, slot),
        }
    }
    let copies: Vec<_> = (0..places.len())
        .map(|at| Copy::between(places[at], places[(at + 1) % places.len()]))
        .collect();
    let moves = plan(&copies, Some(temporary(&copies, Some(Reg::R11)))).unwrap();
    for movement in moves.moves() {
        let CopySource::Place(source) = movement.source();
        match (source, movement.destination()) {
            (Place::Register(src), Place::Register(dst)) => {
                b.mov_reg(dst, src, RegisterWidth::Word);
            }
            (Place::Register(src), Place::Frame(dst)) => b.store_slot(src, dst),
            (Place::Frame(src), Place::Register(dst)) => b.load_slot(dst, src),
            (Place::Frame(src), Place::Frame(dst)) => {
                b.load_slot(Reg::R11, src);
                b.store_slot(Reg::R11, dst);
            }
        }
    }
    for (at, place) in places.into_iter().enumerate() {
        if let Place::Register(reg) = place {
            b.store_slot(reg, FrameSlot::at(u32::try_from(at).unwrap()));
        }
    }
    let mut expected = patterns;
    expected.rotate_right(1);
    assert_eq!(
        capture(b, 6),
        expected
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>()
    );
}

#[test]
fn allocated_instructions_reject_wrong_banks_before_encoding() {
    let mut b = AllocatedBuilder::default();
    b.mov_imm64(Reg::Xmm8, 0);
    assert!(b.finish().unwrap_err().contains("register banks"));
    let mut b = AllocatedBuilder::default();
    b.store(MemoryWidth::Byte, Reg::Xmm0, Reg::Rax, 0);
    assert!(b.finish().unwrap_err().contains("register banks"));
    let mut b = AllocatedBuilder::default();
    b.float(
        Float {
            format: Format::Binary64,
            operation: Operation::Add,
        },
        Reg::Xmm1,
        Reg::Xmm0,
        Some(Reg::Xmm2),
    );
    assert!(b.finish().unwrap_err().contains("register banks"));
}
