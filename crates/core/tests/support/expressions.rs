//! Source-level codegen probes: fold constants normally, but take n from argc.
//! Shared by backend conformance and the 6502 cost measurements.

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
            Self::Chain => "host.exit!(n + three + five)",
            Self::Shared => {
                "a = n + three
                   b = a + n
                   host.exit!(a + b)"
            }
            Self::ConstantLeft => "host.exit!(five + (n + three))",
            // n + 250 crosses 255 at n = 6. Subtracting 255 makes its high
            // byte observable even though an exit status only carries eight
            // bits: a wrongly wrapped sum would yield monus zero instead.
            Self::Carry => {
                "ten = five + five
                   base = five * (five * ten)
                   boundary = base + five
                   sum = n + base
                   host.exit!(sum - boundary)"
            }
            Self::Monus => "host.exit!(n - five)",
        };
        format!(
            "import std.host {{Host}}

             below : (Nat, Nat) -> Bool
             below(_, 0) -> False
             below(0, Succ(_)) -> True
             below(Succ(a), Succ(b)) -> below(a, b)

             finish! : (Host, Bool, Nat) -> []
             finish!(host, False, _) ->
               five = 5
               host.exit!(five * five * 4)
             finish!(host, True, n) ->
               two = 2
               three = two + 1
               five = three + two
               {expression}

             main! : Host -> []
             main!(host) ->
               count = host.args.len()
               finish!(host, below(count, 32), count)"
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
