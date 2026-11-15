//! Written by `FAUN_BLESS=1 cargo nextest run -p faun-cli --test barb_recognition`
//! from the standard's float operations, as the code of each comes to after
//! canonicalizing. Do not edit by hand.

use crate::float::{Float, Format, Operation};

pub(super) const KNOWN: &[(u128, Float)] = &[
    (
        0x19ac_b43f_853f_d44c_91be_61a0_6c97_3870,
        Float {
            operation: Operation::Div,
            format: Format::Binary32,
        },
    ),
    (
        0x1fba_f6e6_8e5f_9714_bfb9_4774_ce99_2ea8,
        Float {
            operation: Operation::Sub,
            format: Format::Binary64,
        },
    ),
    (
        0x2085_5bcb_545a_4d6a_a2fc_2c99_e0ca_b1b3,
        Float {
            operation: Operation::Add,
            format: Format::Binary32,
        },
    ),
    (
        0x2bed_a464_2c52_bcd3_3d19_c827_55cd_8716,
        Float {
            operation: Operation::Add,
            format: Format::Binary64,
        },
    ),
    (
        0x6585_ea24_b5f5_ab80_ba35_00d9_cc04_4d63,
        Float {
            operation: Operation::Div,
            format: Format::Binary64,
        },
    ),
    (
        0x79df_fa0b_9449_f81c_755a_87ca_6667_98b5,
        Float {
            operation: Operation::Sqrt,
            format: Format::Binary32,
        },
    ),
    (
        0xa15f_a57b_8b3b_c50a_2a69_d5b8_cbd2_0862,
        Float {
            operation: Operation::Mul,
            format: Format::Binary64,
        },
    ),
    (
        0xc47e_519b_0853_f95c_cbb3_c217_adec_139d,
        Float {
            operation: Operation::Mul,
            format: Format::Binary32,
        },
    ),
    (
        0xee11_f4a4_de83_14a4_70d6_ae59_7d2a_06ba,
        Float {
            operation: Operation::Sub,
            format: Format::Binary32,
        },
    ),
    (
        0xf607_5e52_575a_7381_5bdb_58d5_0e59_d942,
        Float {
            operation: Operation::Sqrt,
            format: Format::Binary64,
        },
    ),
];
