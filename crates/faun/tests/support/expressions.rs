//! Source-level codegen probes: fold constants normally, but take n from argc.
//! Shared by backend conformance and the 6502 cost measurements.

const LIBRARY: &str = include_str!("../../../../crates/simple/standard/nat.fn");

/// Includes monus and carry boundaries, the last accepted count, and both
/// the guard boundary and a count beyond it. Counts include the program name.
pub(super) const COUNTS: &[u16] = &[1, 2, 4, 5, 6, 15, 16, 17, 31, 32, 33];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Case {
    Chain,
    Shared,
    ConstantLeft,
    Carry,
    Monus,
}

pub(super) const CASES: [Case; 5] = [
    Case::Chain,
    Case::Shared,
    Case::ConstantLeft,
    Case::Carry,
    Case::Monus,
];

impl Case {
    pub(super) fn source(self) -> String {
        let expression = match self {
            Self::Chain => "exit!(h add(add(n three) five))",
            Self::Shared => {
                "a = add(n three)
                 b = add(a n)
                 exit!(h add(a b))"
            }
            Self::ConstantLeft => "exit!(h add(five add(n three)))",
            // n + 250 crosses 255 at n = 6. Subtracting 255 makes its high
            // byte observable even though an exit status only carries eight
            // bits: a wrongly wrapped sum would yield monus zero instead.
            Self::Carry => {
                "ten = add(five five)
                 base = mul(five mul(five ten))
                 boundary = add(base five)
                 sum = add(n base)
                 exit!(h sub(sum boundary))"
            }
            Self::Monus => "exit!(h sub(n five))",
        };
        let natural = |n| format!("{}Zero{}", "Succ(".repeat(n), ")".repeat(n));
        format!(
            "{LIBRARY}

             bounded!(h True n) -> n
             bounded!(h False n) ->
               five = {five}
               exit!(h mul(mul(five five) {four}))

             main!(h) ->
               count = argc!(h)
               n = bounded!(h less_than(count {limit}) count)
               two = Succ(Succ(Zero))
               three = Succ(two)
               five = add(three two)
               {expression}",
            five = natural(5),
            four = natural(4),
            limit = natural(32),
        )
    }

    /// Independent host arithmetic, not the compiler's evaluator. No result
    /// truncation is needed: the carry probe observes the high byte itself.
    pub(super) fn expected(self, argc: u16) -> i32 {
        if argc >= 32 {
            return 100;
        }
        let n = i32::from(argc);
        match self {
            Self::Chain | Self::ConstantLeft => n + 8,
            Self::Shared => 3 * n + 6,
            Self::Carry | Self::Monus => {
                if n < 5 {
                    0
                } else {
                    n - 5
                }
            }
        }
    }
}
