//! Written by `FAUN_BLESS=1 cargo nextest run -p faun --test barb_recognition`
//! from the standard's float operations, as the code of each comes to after
//! canonicalizing. Do not edit by hand.

use faun_base::float::{Float, Format, Operation};

pub(super) const KNOWN: &[(u128, Float)] = &[
    (
        0x0e6a_f736_2c6b_d146_70f5_a230_1ab7_11ae,
        Float {
            operation: Operation::Sub,
            format: Format::Binary64,
        },
    ),
    (
        0x3426_1db0_592f_8fa7_d171_4418_5f10_9db5,
        Float {
            operation: Operation::Mul,
            format: Format::Binary64,
        },
    ),
    (
        0x3db2_2e71_ddeb_a3a2_a851_89a0_7669_4ca6,
        Float {
            operation: Operation::Div,
            format: Format::Binary32,
        },
    ),
    (
        0x6f5b_1649_4973_ab06_96f7_f7df_5ff5_2bd4,
        Float {
            operation: Operation::Add,
            format: Format::Binary64,
        },
    ),
    (
        0x8aa5_fe51_9b6c_8bcb_a218_4a1a_cdc4_fb4f,
        Float {
            operation: Operation::Add,
            format: Format::Binary32,
        },
    ),
    (
        0x9329_e53d_d92c_387d_aa86_c80a_f787_c2bb,
        Float {
            operation: Operation::Sqrt,
            format: Format::Binary64,
        },
    ),
    (
        0x94b1_8cfa_a619_b187_44b0_d295_1cb0_7fd8,
        Float {
            operation: Operation::Mul,
            format: Format::Binary32,
        },
    ),
    (
        0xaf59_aba0_4315_dc10_d1f5_d96f_5373_0e54,
        Float {
            operation: Operation::Sub,
            format: Format::Binary32,
        },
    ),
    (
        0xca98_5385_c073_be73_5750_1284_87fd_3fe2,
        Float {
            operation: Operation::Sqrt,
            format: Format::Binary32,
        },
    ),
    (
        0xd159_d6db_576b_6e6d_d3e9_63b9_d82f_83ef,
        Float {
            operation: Operation::Div,
            format: Format::Binary64,
        },
    ),
];
