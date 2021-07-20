//! This module implements arithmetic over the quadratic extension field Fp12.

use blst::*;

use core::{
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use ff::Field;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{traits::Compress, Fp, Fp2, Fp6};

/// This represents an element $c_0 + c_1 w$ of $\mathbb{F}_{p^12} = \mathbb{F}_{p^6} / w^2 - v$.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Fp12(pub(crate) blst_fp12);

impl fmt::Debug for Fp12 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Fp12")
            .field("c0", &self.c0())
            .field("c1", &self.c1())
            .finish()
    }
}

impl fmt::Display for Fp12 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} + {:?}*u", self.c0(), self.c1())
    }
}

impl From<Fp> for Fp12 {
    fn from(f: Fp) -> Fp12 {
        Fp12::new(Fp6::from(f), Fp6::zero())
    }
}

impl From<Fp2> for Fp12 {
    fn from(f: Fp2) -> Fp12 {
        Fp12::new(Fp6::from(f), Fp6::zero())
    }
}

impl From<Fp6> for Fp12 {
    fn from(f: Fp6) -> Fp12 {
        Fp12::new(f, Fp6::zero())
    }
}

impl From<blst_fp12> for Fp12 {
    fn from(val: blst_fp12) -> Fp12 {
        Fp12(val)
    }
}

impl From<Fp12> for blst_fp12 {
    fn from(val: Fp12) -> blst_fp12 {
        val.0
    }
}

impl ConstantTimeEq for Fp12 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0().ct_eq(&other.c0()) & self.c1().ct_eq(&other.c1())
    }
}

impl ConditionallySelectable for Fp12 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp12(blst_fp12 {
            fp6: [
                Fp6::conditional_select(&a.c0(), &b.c0(), choice).0,
                Fp6::conditional_select(&a.c1(), &b.c1(), choice).0,
            ],
        })
    }
}

impl Default for Fp12 {
    fn default() -> Self {
        Fp12::zero()
    }
}

impl Neg for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn neg(self) -> Fp12 {
        let c0 = -self.c0();
        let c1 = -self.c1();
        Fp12::new(c0, c1)
    }
}

impl Neg for Fp12 {
    type Output = Fp12;

    #[inline]
    fn neg(self) -> Fp12 {
        -&self
    }
}

impl Sub<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn sub(self, rhs: &Fp12) -> Fp12 {
        let c0 = self.c0() - rhs.c0();
        let c1 = self.c1() - rhs.c1();
        Fp12::new(c0, c1)
    }
}

impl Add<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn add(self, rhs: &Fp12) -> Fp12 {
        let c0 = self.c0() + rhs.c0();
        let c1 = self.c1() + rhs.c1();
        Fp12::new(c0, c1)
    }
}

impl Mul<&Fp12> for &Fp12 {
    type Output = Fp12;

    #[inline]
    fn mul(self, rhs: &Fp12) -> Fp12 {
        let mut out = blst_fp12::default();
        unsafe { blst_fp12_mul(&mut out, &self.0, &rhs.0) };
        Fp12(out)
    }
}

impl AddAssign<&Fp12> for Fp12 {
    #[inline]
    fn add_assign(&mut self, rhs: &Fp12) {
        *self = *self + rhs;
    }
}

impl SubAssign<&Fp12> for Fp12 {
    #[inline]
    fn sub_assign(&mut self, rhs: &Fp12) {
        *self = *self - rhs;
    }
}

impl MulAssign<&Fp12> for Fp12 {
    #[inline]
    fn mul_assign(&mut self, rhs: &Fp12) {
        unsafe { blst_fp12_mul(&mut self.0, &self.0, &rhs.0) };
    }
}

impl_add_sub!(Fp12);
impl_add_sub_assign!(Fp12);
impl_mul!(Fp12);
impl_mul_assign!(Fp12);

impl Field for Fp12 {
    fn random(mut rng: impl RngCore) -> Self {
        Fp12::new(Fp6::random(&mut rng), Fp6::random(&mut rng))
    }

    fn zero() -> Self {
        Fp12::new(Fp6::zero(), Fp6::zero())
    }

    fn one() -> Self {
        Fp12::new(Fp6::one(), Fp6::zero())
    }

    fn is_zero(&self) -> bool {
        self.c0().is_zero() && self.c1().is_zero()
    }

    fn double(&self) -> Self {
        self + self
    }

    fn square(&self) -> Self {
        let mut sq = blst_fp12::default();
        unsafe { blst_fp12_sqr(&mut sq, &self.0) };
        Fp12(sq)
    }

    fn invert(&self) -> CtOption<Self> {
        let is_zero = self.ct_eq(&Self::zero());
        let mut inv = blst_fp12::default();
        unsafe { blst_fp12_inverse(&mut inv, &self.0) }
        CtOption::new(Self::default(), !is_zero).map(|_| Fp12(inv))
    }

    fn sqrt(&self) -> CtOption<Self> {
        unimplemented!()
    }
}

impl Fp12 {
    /// Constructs an element of `Fp12`.
    pub const fn new(c0: Fp6, c1: Fp6) -> Fp12 {
        Fp12(blst_fp12 { fp6: [c0.0, c1.0] })
    }

    pub fn frobenius_map(&mut self, power: usize) {
        // TODO: switch to blst version when it matches
        // unsafe { blst_fp12_frobenius_map(&mut out, &self.0, power) }

        let mut c0 = self.c0();
        c0.frobenius_map(power);
        let mut c1 = self.c1();
        c1.frobenius_map(power);

        let mut c0_raw = blst_fp2::default();
        let mut c1_raw = blst_fp2::default();
        let mut c2_raw = blst_fp2::default();
        unsafe {
            blst_fp2_mul(
                &mut c0_raw,
                &c1.0.fp2[0],
                &FROBENIUS_COEFF_FP12_C1[power % 12],
            );
            blst_fp2_mul(
                &mut c1_raw,
                &c1.0.fp2[1],
                &FROBENIUS_COEFF_FP12_C1[power % 12],
            );
            blst_fp2_mul(
                &mut c2_raw,
                &c1.0.fp2[2],
                &FROBENIUS_COEFF_FP12_C1[power % 12],
            );
        }
        c1.0.fp2 = [c0_raw, c1_raw, c2_raw];

        self.0.fp6 = [c0.0, c1.0];
    }

    pub fn c0(&self) -> Fp6 {
        Fp6(self.0.fp6[0])
    }

    pub fn c1(&self) -> Fp6 {
        Fp6(self.0.fp6[1])
    }

    pub fn conjugate(&mut self) {
        unsafe { blst_fp12_conjugate(&mut self.0) };
    }

    fn is_cyc(&self) -> bool {
        // Check if a^(p^4 - p^2 + 1) == 1.
        let mut t0 = *self;
        t0.frobenius_map(4);
        t0 *= self;
        let mut t1 = *self;
        t1.frobenius_map(2);

        t0 == t1
    }

    /// Compress this point. Returns `None` if the element is not in the cyclomtomic subgroup.
    pub fn compress(&self) -> Option<Fp12Compressed> {
        if !self.is_cyc() {
            return None;
        }

        // Use torus-based compression from Section 4.1 in
        // "On Compressible Pairings and Their Computation" by Naehrig et al.
        let mut c0 = self.c0();

        c0.0.fp2[0] = (c0.c0() + Fp2::from(1)).0;
        let b = c0 * self.c1().invert().unwrap();

        Some(Fp12Compressed(b))
    }
}

/// Compressed representation of `Fp12`.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Fp12Compressed(Fp6);

impl fmt::Debug for Fp12Compressed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Fp12Compressed")
            .field("c0", &self.0)
            .finish()
    }
}

impl Fp12Compressed {
    /// Uncompress the given Fp12 element, returns `None` if the element is an invalid compression
    /// format.
    pub fn uncompress(self) -> Option<Fp12> {
        // Formula for decompression for the odd q case from Section 2 in
        // "Compression in finite fields and torus-based cryptography" by
        // Rubin-Silverberg.
        let fp6_neg_one = Fp6::from(1).neg();
        let t = Fp12::new(self.0, fp6_neg_one).invert().unwrap();
        let mut c = Fp12::new(self.0, Fp6::from(1));
        c *= t;

        if c.is_cyc() {
            return Some(c);
        }

        None
    }
}

impl Compress for Fp12 {
    fn write_compressed<W: std::io::Write>(self, mut out: W) -> std::io::Result<()> {
        let c = self.compress().unwrap();

        out.write_all(&c.0.c0().c0().to_bytes_le())?;
        out.write_all(&c.0.c0().c1().to_bytes_le())?;

        out.write_all(&c.0.c1().c0().to_bytes_le())?;
        out.write_all(&c.0.c1().c1().to_bytes_le())?;

        out.write_all(&c.0.c2().c0().to_bytes_le())?;
        out.write_all(&c.0.c2().c1().to_bytes_le())?;

        Ok(())
    }

    fn read_compressed<R: std::io::Read>(mut source: R) -> std::io::Result<Self> {
        let mut buffer = [0u8; 48];
        let read_fp = |source: &mut dyn std::io::Read, buffer: &mut [u8; 48]| {
            source.read_exact(buffer)?;
            let fp = Fp::from_bytes_le(buffer);
            fp.ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid fp"))
        };

        let x0 = read_fp(&mut source, &mut buffer)?;
        let x1 = read_fp(&mut source, &mut buffer)?;

        let y0 = read_fp(&mut source, &mut buffer)?;
        let y1 = read_fp(&mut source, &mut buffer)?;

        let z0 = read_fp(&mut source, &mut buffer)?;
        let z1 = read_fp(&mut source, &mut buffer)?;

        let x = Fp2::new(x0, x1);
        let y = Fp2::new(y0, y1);
        let z = Fp2::new(z0, z1);

        let compressed = Fp12Compressed(Fp6::new(x, y, z));
        compressed.uncompress().ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid compression point")
        })
    }
}

// non_residue^((modulus^i-1)/6) for i=0,...,11
const FROBENIUS_COEFF_FP12_C1: [blst_fp2; 12] = [
    // Fp2(u + 1)**(((q^0) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x760900000002fffd,
                    0xebf4000bc40c0002,
                    0x5f48985753c758ba,
                    0x77ce585370525745,
                    0x5c071a97a256ec6d,
                    0x15f65ec3fa80e493,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^1) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x7089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x8f2220fb0fb66eb,
                ],
            },
            blst_fp {
                l: [
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^2) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xecfb361b798dba3a,
                    0xc100ddb891865a2c,
                    0xec08ff1232bda8e,
                    0xd5c13cc6f1ca4721,
                    0x47222a47bf7b5c04,
                    0x110f184e51c5f59,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^3) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0xbd592fc7d825ec8,
                ],
            },
            blst_fp {
                l: [
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0xe2b7eedbbfd87d2,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^4) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x30f1361b798a64e8,
                    0xf3b8ddab7ece5a2a,
                    0x16a8ca3ac61577f7,
                    0xc26a2ff874fd029b,
                    0x3636b76660701c6e,
                    0x51ba4ab241b6160,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^5) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x95ba654ed2226b,
                    0x2e370eccc86f7dd,
                ],
            },
            blst_fp {
                l: [
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^6) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x43f5fffffffcaaae,
                    0x32b7fff2ed47fffd,
                    0x7e83a49a2e99d69,
                    0xeca8f3318332bb7a,
                    0xef148d1ea0f4c069,
                    0x40ab3263eff0206,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^7) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ],
            },
            blst_fp {
                l: [
                    0x7089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x8f2220fb0fb66eb,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^8) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0xcd03c9e48671f071,
                    0x5dab22461fcda5d2,
                    0x587042afd3851b95,
                    0x8eb60ebe01bacb9e,
                    0x3f97d6e83d050d2,
                    0x18f0206554638741,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^9) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0xe2b7eedbbfd87d2,
                ],
            },
            blst_fp {
                l: [
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0xbd592fc7d825ec8,
                ],
            },
        ],
    },
    // Fp2(u + 1)**(((q^10) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x890dc9e4867545c3,
                    0x2af322533285a5d5,
                    0x50880866309b7e2c,
                    0xa20d1b8c7e881024,
                    0x14e4f04fe2db9068,
                    0x14e56d3f1564853a,
                ],
            },
            blst_fp {
                l: [0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
            },
        ],
    },
    // Fp2(u + 1)**(((q^11) - 1) / 6)
    blst_fp2 {
        fp: [
            blst_fp {
                l: [
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ],
            },
            blst_fp {
                l: [
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x95ba654ed2226b,
                    0x2e370eccc86f7dd,
                ],
            },
        ],
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    use ff::PrimeField;
    use group::{Curve, Group};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use crate::{G1Projective, G2Projective};

    #[test]
    fn test_fp12_eq() {
        assert_eq!(Fp12::one(), Fp12::one());
        assert_eq!(Fp12::zero(), Fp12::zero());
        assert_ne!(Fp12::zero(), Fp12::one());
    }

    #[test]
    fn fp12_random_frobenius_tests() {
        use std::convert::TryFrom;

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let characteristic: Vec<u64> = Fp::char()
            .chunks(8)
            .map(|chunk| u64::from_le_bytes(<[u8; 8]>::try_from(chunk).unwrap()))
            .collect();

        let maxpower = 13;

        for _ in 0..100 {
            for i in 0..(maxpower + 1) {
                let mut a = Fp12::random(&mut rng);
                let mut b = a;

                for _ in 0..i {
                    a = a.pow_vartime(&characteristic);
                }
                b.frobenius_map(i);

                assert_eq!(a, b);
            }
        }
    }

    #[test]
    fn fp12_random_field_tests() {
        crate::tests::field::random_field_tests::<Fp12>();
    }

    #[test]
    fn fp12_compression() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..100 {
            let a = Fp12::random(&mut rng);
            // usually not cyclomatic, so not compressable
            if let Some(b) = a.compress() {
                let c = b.uncompress().unwrap();
                assert_eq!(a, c, "{}", i);
            } else {
                println!("skipping {}", i);
            }

            // pairing result, should be compressable
            let p = G1Projective::random(&mut rng).to_affine();
            let q = G2Projective::random(&mut rng).to_affine();
            let a = crate::pairing(&p, &q);
            assert!(a.is_cyc());

            let b = a.compress().unwrap();
            let c = b.uncompress().unwrap();
            assert_eq!(a, c, "{}", i);

            let mut buffer = Vec::new();
            a.write_compressed(&mut buffer).unwrap();
            let out = Fp12::read_compressed(std::io::Cursor::new(buffer)).unwrap();
            assert_eq!(a, out);
        }
    }
}
