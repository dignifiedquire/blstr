use core::ops::Mul;

use ff::{Field, PrimeField};
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, GroupOps, GroupOpsOwned, ScalarMul, ScalarMulOwned,
    UncompressedEncoding, WnafGroup,
};

/// This traits enables reading and writing a compressed version.
pub trait Compress: Sized {
    fn write_compressed<W: std::io::Write>(self, out: W) -> std::io::Result<()>;
    fn read_compressed<R: std::io::Read>(source: R) -> std::io::Result<Self>;
}
