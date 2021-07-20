#![allow(dead_code)]
#![allow(unused_imports)]

#[macro_use]
mod macros;

mod fp;
mod fp12;
mod fp2;
mod fp6;
mod g1;
mod g2;
mod gt;
mod pairing;
mod scalar;
mod traits;

pub use fp::Fp;
pub use fp12::Fp12;
pub use fp2::Fp2;
pub use fp6::Fp6;
pub use g1::{G1Affine, G1Compressed, G1Projective, G1Uncompressed};
pub use g2::{G2Affine, G2Compressed, G2Prepared, G2Projective, G2Uncompressed};
pub use gt::Gt;
pub use pairing::pairing;
pub use scalar::Scalar;
pub use traits::Compress;

mod serde_impl;

#[cfg(test)]
mod tests;

use blst::*;
use ff::Field;
use pairing_lib::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};

/// Bls12-381 engine
#[derive(Debug, Copy, Clone)]
pub struct Bls12;

impl Engine for Bls12 {
    type Fr = Scalar;
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        Gt(pairing(p, q).0)
    }
}

impl MillerLoopResult for Fp12 {
    type Gt = Gt;

    fn final_exponentiation(&self) -> Self::Gt {
        let mut out = blst_fp12::default();
        unsafe { blst_final_exp(&mut out, &self.0) };
        Gt(out)
    }
}

impl MultiMillerLoop for Bls12 {
    type G2Prepared = G2Prepared;
    type Result = Fp12;

    /// Computes $$\sum_{i=1}^n \textbf{ML}(a_i, b_i)$$ given a series of terms
    /// $$(a_1, b_1), (a_2, b_2), ..., (a_n, b_n).$$
    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        let mut res = blst::blst_fp12::default();

        for (i, (p, q)) in terms.into_iter().enumerate() {
            let mut tmp = blst::blst_fp12::default();
            if q.is_zero() || p.is_zero() {
                // Define pairing with zero as one, matching what `pairing` does.
                tmp = Fp12::one().0;
            } else {
                unsafe {
                    blst::blst_miller_loop_lines(&mut tmp, q.lines.as_ptr(), &p.0);
                }
            }
            if i == 0 {
                res = tmp;
            } else {
                unsafe {
                    blst::blst_fp12_mul(&mut res, &res, &tmp);
                }
            }
        }

        Fp12(res)
    }
}

#[test]
fn bls12_engine_tests() {
    crate::tests::engine::engine_tests::<Bls12>();
}
