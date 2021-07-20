//! An implementation of the BLS12-381 scalar field $\mathbb{F}_q$
//! where `q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`

use core::{
    cmp,
    convert::TryFrom,
    fmt, mem,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use ff::{Field, PrimeField};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Represents an element of the scalar field $\mathbb{F}_q$ of the BLS12-381 elliptic
/// curve construction.
///
/// The inner representation `blst_fr` is stored in Montgomery form as little-endian `u64` limbs.
#[derive(Default, Clone, Copy)]
pub struct Scalar(pub(crate) blst_fr);

// Little-endian non-Montgomery form not reduced mod p.
#[allow(dead_code)]
const MODULUS: [u64; 4] = [
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

// Little-endian non-Montgomery form not reduced mod p.
const MODULUS_REPR: [u8; 32] = [
    0x01, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0x02, 0xa4, 0xbd, 0x53,
    0x05, 0xd8, 0xa1, 0x09, 0x08, 0xd8, 0x39, 0x33, 0x48, 0x7d, 0x9d, 0x29, 0x53, 0xa7, 0xed, 0x73,
];

// `2^S` root of unity in little-endian Montgomery form.
const ROOT_OF_UNITY: Scalar = Scalar(blst_fr {
    l: [
        0xb9b5_8d8c_5f0e_466a,
        0x5b1b_4c80_1819_d7ec,
        0x0af5_3ae3_52a3_1e64,
        0x5bf3_adda_19e9_b27b,
    ],
});

/// `R = 2^256 mod q` in little-endian Montgomery form which is equivalent to 1 in little-endian
/// non-Montgomery form.
///
/// sage> mod(2^256, 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
/// sage> 0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe
const R: Scalar = Scalar(blst_fr {
    l: [
        0x0000_0001_ffff_fffe,
        0x5884_b7fa_0003_4802,
        0x998c_4fef_ecbc_4ff5,
        0x1824_b159_acc5_056f,
    ],
});

/// `R^2 = 2^512 mod q` in little-endian Montgomery form.
///
/// sage> mod(2^512, 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
/// sage> 0x748d9d99f59ff1105d314967254398f2b6cedcb87925c23c999e990f3f29c6d
const R2: Scalar = Scalar(blst_fr {
    l: [
        0xc999_e990_f3f2_9c6d,
        0x2b6c_edcb_8792_5c23,
        0x05d3_1496_7254_398f,
        0x0748_d9d9_9f59_ff11,
    ],
});

/// `R^3 = 2^768 mod q` in little-endian Montgomery form.
///
/// sage> mod(2^768, 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
/// sage> 0x6e2a5bb9c8db33e973d13c71c7b5f4181b3e0d188cf06990c62c1807439b73af
const R3: Scalar = Scalar(blst_fr {
    l: [
        0xc62c_1807_439b_73af,
        0x1b3e_0d18_8cf0_6990,
        0x73d1_3c71_c7b5_f418,
        0x6e2a_5bb9_c8db_33e9,
    ],
});

pub const S: u32 = 32;

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let be_bytes = self.to_bytes_be();
        write!(f, "Scalar(0x")?;
        for &b in be_bytes.iter() {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl fmt::Display for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Ord for Scalar {
    fn cmp(&self, other: &Scalar) -> cmp::Ordering {
        for (a, b) in self.to_bytes_be().iter().zip(other.to_bytes_be().iter()) {
            if a > b {
                return cmp::Ordering::Greater;
            } else if a < b {
                return cmp::Ordering::Less;
            }
        }
        cmp::Ordering::Equal
    }
}

impl PartialOrd for Scalar {
    #[inline(always)]
    fn partial_cmp(&self, other: &Scalar) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Scalar {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.l == other.0.l
    }
}

impl Eq for Scalar {}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.l[0].ct_eq(&other.0.l[0])
            & self.0.l[1].ct_eq(&other.0.l[1])
            & self.0.l[2].ct_eq(&other.0.l[2])
            & self.0.l[3].ct_eq(&other.0.l[3])
    }
}

impl ConditionallySelectable for Scalar {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Scalar(blst_fr {
            l: [
                u64::conditional_select(&a.0.l[0], &b.0.l[0], choice),
                u64::conditional_select(&a.0.l[1], &b.0.l[1], choice),
                u64::conditional_select(&a.0.l[2], &b.0.l[2], choice),
                u64::conditional_select(&a.0.l[3], &b.0.l[3], choice),
            ],
        })
    }
}

impl From<Scalar> for blst_fr {
    fn from(val: Scalar) -> blst_fr {
        val.0
    }
}

impl From<blst_fr> for Scalar {
    fn from(val: blst_fr) -> Scalar {
        Scalar(val)
    }
}

impl From<u64> for Scalar {
    fn from(val: u64) -> Scalar {
        let mut repr = [0u8; 32];
        repr[..8].copy_from_slice(&val.to_le_bytes());
        Scalar::from_bytes_le(&repr).unwrap()
    }
}

impl Neg for &Scalar {
    type Output = Scalar;

    #[inline]
    fn neg(self) -> Scalar {
        let mut neg = blst_fr::default();
        unsafe { blst_fr_cneg(&mut neg, &self.0, true) };
        Scalar(neg)
    }
}

impl Neg for Scalar {
    type Output = Scalar;

    #[inline]
    fn neg(self) -> Scalar {
        -&self
    }
}

impl Add<&Scalar> for &Scalar {
    type Output = Scalar;

    #[inline]
    fn add(self, rhs: &Scalar) -> Scalar {
        let mut out = blst_fr::default();
        unsafe { blst_fr_add(&mut out, &self.0, &rhs.0) };
        Scalar(out)
    }
}

impl Sub<&Scalar> for &Scalar {
    type Output = Scalar;

    #[inline]
    fn sub(self, rhs: &Scalar) -> Scalar {
        let mut out = blst_fr::default();
        unsafe { blst_fr_sub(&mut out, &self.0, &rhs.0) };
        Scalar(out)
    }
}

impl Mul<&Scalar> for &Scalar {
    type Output = Scalar;

    #[inline]
    fn mul(self, rhs: &Scalar) -> Scalar {
        let mut out = blst_fr::default();
        unsafe { blst_fr_mul(&mut out, &self.0, &rhs.0) };
        Scalar(out)
    }
}

impl AddAssign<&Scalar> for Scalar {
    #[inline]
    fn add_assign(&mut self, rhs: &Scalar) {
        unsafe { blst_fr_add(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&Scalar> for Scalar {
    #[inline]
    fn sub_assign(&mut self, rhs: &Scalar) {
        unsafe { blst_fr_sub(&mut self.0, &self.0, &rhs.0) };
    }
}

impl MulAssign<&Scalar> for Scalar {
    #[inline]
    fn mul_assign(&mut self, rhs: &Scalar) {
        unsafe { blst_fr_mul(&mut self.0, &self.0, &rhs.0) };
    }
}

impl_add_sub!(Scalar);
impl_add_sub_assign!(Scalar);
impl_mul!(Scalar);
impl_mul_assign!(Scalar);

/// The number of bits we should "shave" from a randomly sampled reputation.
const REPR_SHAVE_BITS: usize = 256 - Scalar::NUM_BITS as usize;

impl Field for Scalar {
    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let mut raw = [0u64; 4];
            for i in 0..4 {
                raw[i] = rng.next_u64();
            }

            // Mask away the unused most-significant bits.
            raw[3] &= 0xffffffffffffffff >> REPR_SHAVE_BITS;

            if let Some(scalar) = Scalar::from_u64s_le(&raw) {
                return scalar;
            }
        }
    }

    fn zero() -> Self {
        Scalar(blst_fr { l: [0, 0, 0, 0] })
    }

    fn one() -> Self {
        R
    }

    fn is_zero(&self) -> bool {
        self.0.l == [0, 0, 0, 0]
    }

    fn square(&self) -> Self {
        let mut sq = blst_fr::default();
        unsafe { blst_fr_sqr(&mut sq, &self.0) }
        Scalar(sq)
    }

    fn double(&self) -> Self {
        self + self
    }

    fn invert(&self) -> CtOption<Self> {
        let mut inv = blst_fr::default();
        unsafe { blst_fr_eucl_inverse(&mut inv, &self.0) };
        let is_invertible = !self.ct_eq(&Scalar::zero());
        CtOption::new(Scalar(inv), is_invertible)
    }

    /// Warning: this is not constant-time.
    fn sqrt(&self) -> CtOption<Self> {
        // Tonelli-Shank's algorithm for q mod 16 = 1
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        match self.legendre() {
            0 => return CtOption::new(*self, Choice::from(1)),
            -1 => return CtOption::new(Scalar::default(), Choice::from(0)),
            _ => {}
        };

        let mut c = Self::root_of_unity();
        let mut r = self.pow_vartime([
            9223141137265459200,
            347036667491570177,
            10722717374829358084,
            972477353,
        ]);
        let mut t = self.pow_vartime([
            18446282274530918399,
            694073334983140354,
            2998690675949164552,
            1944954707,
        ]);
        let mut m = S;

        while t != Self::one() {
            let mut i = 1;
            {
                let mut t2i = t;
                t2i = t2i.square();
                loop {
                    if t2i == Self::one() {
                        break;
                    }
                    t2i = t2i.square();
                    i += 1;
                }
            }

            for _ in 0..(m - i - 1) {
                c = c.square();
            }
            r *= &c;
            c = c.square();
            t *= &c;
            m = i;
        }

        CtOption::new(r, Choice::from(1))
    }
}

impl PrimeField for Scalar {
    // Little-endian non-Montgomery form bigint mod p.
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 255;
    const CAPACITY: u32 = Self::NUM_BITS - 1;
    const S: u32 = S;

    /// Converts a little-endian non-Montgomery form `repr` into a Montgomery form `Scalar`.
    fn from_repr(repr: Self::Repr) -> Option<Self> {
        Self::from_bytes_le(&repr)
    }

    /// Converts a Montgomery form `Scalar` into little-endian non-Montgomery from.
    fn to_repr(&self) -> Self::Repr {
        self.to_bytes_le()
    }

    fn is_odd(&self) -> bool {
        self.to_repr()[0] & 1 == 1
    }

    fn multiplicative_generator() -> Self {
        Scalar::from(7)
    }

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

// Returns `true` if  `le_bytes` is less than the modulus (both are in non-Montgomery form).
fn is_valid(le_bytes: &[u8; 32]) -> bool {
    for (a, b) in le_bytes.iter().zip(MODULUS_REPR.iter()).rev() {
        if a > b {
            return false;
        } else if a < b {
            return true;
        }
    }
    // Return `false` if `le_bytes` is the modulus.
    false
}

impl Scalar {
    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Scalar`, failing if the input is not canonical.
    pub fn from_bytes_le(bytes: &[u8; 32]) -> Option<Scalar> {
        let mut raw = blst_scalar::default();
        let mut out = blst_fr::default();
        unsafe {
            blst_scalar_from_lendian(&mut raw, bytes.as_ptr());
            if !blst_scalar_fr_check(&raw) {
                return None;
            }
            blst_fr_from_scalar(&mut out, &raw);
        };
        Some(Scalar(out))
    }

    /// Attempts to convert a big-endian byte representation of
    /// a scalar into a `Scalar`, failing if the input is not canonical.
    pub fn from_bytes_be(be_bytes: &[u8; 32]) -> Option<Scalar> {
        let mut le_bytes = *be_bytes;
        le_bytes.reverse();
        Self::from_bytes_le(&le_bytes)
    }

    /// Converts an element of `Scalar` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        let mut repr = [0u8; 32];
        let mut scalar = blst_scalar::default();
        unsafe {
            blst_scalar_from_fr(&mut scalar, &self.0);
            blst_lendian_from_scalar(repr.as_mut_ptr(), &scalar);
        }
        repr
    }

    /// Converts an element of `Scalar` into a byte representation in
    /// big-endian byte order.
    pub fn to_bytes_be(&self) -> [u8; 32] {
        let mut bytes = self.to_bytes_le();
        bytes.reverse();
        bytes
    }

    // `u64s` represent a little-endian non-Montgomery form integer mod p.
    pub fn from_u64s_le(u64s: &[u64; 4]) -> Option<Self> {
        let mut le_bytes = [0u8; 32];
        le_bytes[..8].copy_from_slice(&u64s[0].to_le_bytes());
        le_bytes[8..16].copy_from_slice(&u64s[1].to_le_bytes());
        le_bytes[16..24].copy_from_slice(&u64s[2].to_le_bytes());
        le_bytes[24..].copy_from_slice(&u64s[3].to_le_bytes());
        Scalar::from_bytes_le(&le_bytes)
    }

    pub fn is_quad_res(&self) -> bool {
        match self.legendre() {
            0 | 1 => true,
            _ => false,
        }
    }

    fn legendre(&self) -> i8 {
        const MOD_MINUS_1_OVER_2: [u64; 4] = [
            0x7fffffff80000000,
            0xa9ded2017fff2dff,
            0x199cec0404d0ec02,
            0x39f6d3a994cebea4,
        ];
        // s = self^((modulus - 1) // 2)
        let s = self.pow_vartime(MOD_MINUS_1_OVER_2);
        if s == Self::zero() {
            0
        } else if s == Self::one() {
            1
        } else {
            -1
        }
    }

    pub fn is_even(&self) -> bool {
        !self.is_odd()
    }

    pub fn char() -> <Self as PrimeField>::Repr {
        MODULUS_REPR
    }

    pub fn num_bits(&self) -> u32 {
        let mut ret = 256;
        for i in self.to_bytes_be().iter() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 8 {
                break;
            }
        }

        ret
    }

    /// Multiplies `self` with `3`, returning the result.
    pub fn mul3(&self) -> Self {
        let mut out = blst_fr::default();

        unsafe { blst_fr_mul_by_3(&mut out, &self.0) };

        Scalar(out)
    }

    /// Left shift `self` by `count`, returning the result.
    pub fn shl(&self, count: usize) -> Self {
        let mut out = blst_fr::default();

        unsafe { blst_fr_lshift(&mut out, &self.0, count) };

        Scalar(out)
    }

    /// Right shift `self` by `count`, returning the result.
    pub fn shr(&self, count: usize) -> Self {
        let mut out = blst_fr::default();

        unsafe { blst_fr_rshift(&mut out, &self.0, count) };

        Scalar(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    /// INV = -(q^{-1} mod 2^64) mod 2^64
    const INV: u64 = 0xfffffffeffffffff;

    const LARGEST: Scalar = Scalar(blst::blst_fr {
        l: [
            0xffffffff00000000,
            0x53bda402fffe5bfe,
            0x3339d80809a1d805,
            0x73eda753299d7d48,
        ],
    });

    #[test]
    fn test_inv() {
        // Compute -(q^{-1} mod 2^64) mod 2^64 by exponentiating
        // by totient(2**64) - 1

        let mut inv = 1u64;
        for _ in 0..63 {
            inv = inv.wrapping_mul(inv);
            inv = inv.wrapping_mul(MODULUS[0]);
        }
        inv = inv.wrapping_neg();

        assert_eq!(inv, INV);
    }

    #[test]
    fn test_debug() {
        assert_eq!(
            format!("{:?}", Scalar::zero()),
            "Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)"
        );
        assert_eq!(
            format!("{:?}", Scalar::one()),
            "Scalar(0x0000000000000000000000000000000000000000000000000000000000000001)"
        );
        assert_eq!(
            format!("{:?}", R2),
            "Scalar(0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe)"
        );
    }

    #[test]
    fn test_equality() {
        assert_eq!(Scalar::zero(), Scalar::zero());
        assert_eq!(Scalar::one(), Scalar::one());
        assert_eq!(R2, R2);

        assert_ne!(Scalar::zero(), Scalar::one());
        assert_ne!(Scalar::one(), R2);
    }

    #[test]
    fn test_to_bytes() {
        assert_eq!(
            Scalar::zero().to_bytes_le(),
            [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );

        assert_eq!(
            Scalar::one().to_bytes_le(),
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );

        assert_eq!(
            R2.to_bytes_le(),
            [
                254, 255, 255, 255, 1, 0, 0, 0, 2, 72, 3, 0, 250, 183, 132, 88, 245, 79, 188, 236,
                239, 79, 140, 153, 111, 5, 197, 172, 89, 177, 36, 24
            ]
        );

        assert_eq!(
            (-&Scalar::one()).to_bytes_le(),
            [
                0, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9,
                8, 216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
            ]
        );
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(
            Scalar::from_bytes_le(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ])
            .unwrap(),
            Scalar::zero()
        );

        assert_eq!(
            Scalar::from_bytes_le(&[
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ])
            .unwrap(),
            Scalar::one()
        );

        assert_eq!(
            Scalar::from_bytes_le(&[
                254, 255, 255, 255, 1, 0, 0, 0, 2, 72, 3, 0, 250, 183, 132, 88, 245, 79, 188, 236,
                239, 79, 140, 153, 111, 5, 197, 172, 89, 177, 36, 24
            ])
            .unwrap(),
            R2,
        );

        // -1 should work
        assert!(Scalar::from_bytes_le(&[
            0, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_some());

        // modulus is invalid
        assert!(Scalar::from_bytes_le(&MODULUS_REPR).is_none());

        // Anything larger than the modulus is invalid
        assert!(Scalar::from_bytes_le(&[
            2, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_none());
        assert!(Scalar::from_bytes_le(&[
            1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 58, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_none());
        assert!(Scalar::from_bytes_le(&[
            1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 116
        ])
        .is_none());
    }

    #[test]
    fn test_zero() {
        assert_eq!(Scalar::zero(), -&Scalar::zero());
        assert_eq!(Scalar::zero(), Scalar::zero() + Scalar::zero());
        assert_eq!(Scalar::zero(), Scalar::zero() - Scalar::zero());
        assert_eq!(Scalar::zero(), Scalar::zero() * Scalar::zero());
    }

    #[test]
    fn test_addition() {
        let mut tmp = LARGEST;
        tmp += &LARGEST;

        assert_eq!(
            tmp,
            Scalar(blst::blst_fr {
                l: [
                    0xfffffffeffffffff,
                    0x53bda402fffe5bfe,
                    0x3339d80809a1d805,
                    0x73eda753299d7d48
                ]
            })
        );

        let mut tmp = LARGEST;
        tmp += &Scalar(blst::blst_fr { l: [1, 0, 0, 0] });

        assert_eq!(tmp, Scalar::zero());
    }

    #[test]
    fn test_negation() {
        let tmp = -&LARGEST;

        assert_eq!(tmp, Scalar(blst::blst_fr { l: [1, 0, 0, 0] }));

        let tmp = -&Scalar::zero();
        assert_eq!(tmp, Scalar::zero());
        let tmp = -&Scalar(blst::blst_fr { l: [1, 0, 0, 0] });
        assert_eq!(tmp, LARGEST);

        {
            let mut a = Scalar::zero();
            a = -a;

            assert!(a.is_zero());
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure (a - (-a)) = 0.
            let mut a = Scalar::random(&mut rng);
            let mut b = a;
            b = -b;
            a += &b;

            assert!(a.is_zero());
        }
    }

    #[test]
    fn test_subtraction() {
        let mut tmp = LARGEST;
        tmp -= &LARGEST;

        assert_eq!(tmp, Scalar::zero());

        let mut tmp = Scalar::zero();
        tmp -= &LARGEST;

        let mut tmp2 = Scalar(blst::blst_fr { l: MODULUS });
        tmp2 -= &LARGEST;

        assert_eq!(tmp, tmp2);
    }

    #[test]
    fn test_multiplication() {
        let mut tmp = Scalar(blst::blst_fr {
            l: [
                0x6b7e9b8faeefc81a,
                0xe30a8463f348ba42,
                0xeff3cb67a8279c9c,
                0x3d303651bd7c774d,
            ],
        });
        tmp *= &Scalar(blst::blst_fr {
            l: [
                0x13ae28e3bc35ebeb,
                0xa10f4488075cae2c,
                0x8160e95a853c3b5d,
                0x5ae3f03b561a841d,
            ],
        });
        assert!(
            tmp == Scalar(blst::blst_fr {
                l: [
                    0x23717213ce710f71,
                    0xdbee1fe53a16e1af,
                    0xf565d3e1c2a48000,
                    0x4426507ee75df9d7
                ]
            })
        );

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000000 {
            // Ensure that (a * b) * c = a * (b * c)
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let c = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1 *= &b;
            tmp1 *= &c;

            let mut tmp2 = b;
            tmp2 *= &c;
            tmp2 *= &a;

            assert_eq!(tmp1, tmp2);
        }

        for _ in 0..1000000 {
            // Ensure that r * (a + b + c) = r*a + r*b + r*c

            let r = Scalar::random(&mut rng);
            let mut a = Scalar::random(&mut rng);
            let mut b = Scalar::random(&mut rng);
            let mut c = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1 += &b;
            tmp1 += &c;
            tmp1 *= &r;

            a *= &r;
            b *= &r;
            c *= &r;

            a += &b;
            a += &c;

            assert_eq!(tmp1, a);
        }
    }

    #[test]
    fn test_inverse_is_pow() {
        let q_minus_2 = [
            0xfffffffeffffffff,
            0x53bda402fffe5bfe,
            0x3339d80809a1d805,
            0x73eda753299d7d48,
        ];

        let mut r1 = R;
        let mut r2 = r1;

        for _ in 0..100 {
            r1 = r1.invert().unwrap();
            r2 = r2.pow_vartime(&q_minus_2);

            assert_eq!(r1, r2);
            // Add R so we check something different next time around
            r1 += R;
            r2 = r1;
        }
    }

    #[test]
    fn test_sqrt() {
        {
            assert_eq!(Scalar::zero().sqrt().unwrap(), Scalar::zero());
        }

        let mut square = Scalar(blst::blst_fr {
            l: [
                0x46cd85a5f273077e,
                0x1d30c47dd68fc735,
                0x77f656f60beca0eb,
                0x494aa01bdf32468d,
            ],
        });

        let mut none_count = 0;

        for _ in 0..100 {
            let square_root = square.sqrt();
            if square_root.is_none().into() {
                none_count += 1;
            } else {
                assert_eq!(square_root.unwrap() * square_root.unwrap(), square);
            }
            square -= Scalar::one();
        }

        assert_eq!(49, none_count);
    }

    #[test]
    fn test_double() {
        let a = Scalar::from_u64s_le(&[
            0x1fff3231233ffffd,
            0x4884b7fa00034802,
            0x998c4fefecbc4ff3,
            0x1824b159acc50562,
        ])
        .unwrap();

        assert_eq!(a.double(), a + a);
    }

    #[test]
    fn test_scalar_ordering() {
        fn assert_equality(a: Scalar, b: Scalar) {
            assert_eq!(a, b);
            assert!(a.cmp(&b) == core::cmp::Ordering::Equal);
        }

        fn assert_lt(a: Scalar, b: Scalar) {
            assert!(a < b);
            assert!(b > a);
        }

        assert_equality(
            Scalar::from_u64s_le(&[9999, 9999, 9999, 9999]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9999, 9999, 9999]).unwrap(),
        );
        assert_equality(
            Scalar::from_u64s_le(&[9999, 9998, 9999, 9999]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9998, 9999, 9999]).unwrap(),
        );
        assert_equality(
            Scalar::from_u64s_le(&[9999, 9999, 9999, 9997]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9999, 9999, 9997]).unwrap(),
        );
        assert_lt(
            Scalar::from_u64s_le(&[9999, 9997, 9999, 9998]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9997, 9999, 9999]).unwrap(),
        );
        assert_lt(
            Scalar::from_u64s_le(&[9999, 9997, 9998, 9999]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9997, 9999, 9999]).unwrap(),
        );
        assert_lt(
            Scalar::from_u64s_le(&[9, 9999, 9999, 9997]).unwrap(),
            Scalar::from_u64s_le(&[9999, 9999, 9999, 9997]).unwrap(),
        );
    }

    #[test]
    fn test_scalar_from_u64() {
        let a = Scalar::from(100);
        let mut expected_bytes = [0u8; 32];
        expected_bytes[0] = 100;
        assert_eq!(a.to_bytes_le(), expected_bytes);
    }

    #[test]
    fn test_scalar_is_odd() {
        assert!(Scalar::from(0).is_even());
        assert!(Scalar::from(1).is_odd());
        assert!(Scalar::from(324834872).is_even());
        assert!(Scalar::from(324834873).is_odd());
    }

    #[test]
    fn test_scalar_is_zero() {
        assert!(Scalar::from(0).is_zero());
        assert!(!Scalar::from(1).is_zero());
        assert!(!Scalar::from_u64s_le(&[0, 0, 1, 0]).unwrap().is_zero());
    }

    #[test]
    fn test_scalar_num_bits() {
        assert_eq!(Scalar::NUM_BITS, 255);
        assert_eq!(Scalar::CAPACITY, 254);

        let mut a = Scalar::from(0);
        assert_eq!(0, a.num_bits());
        a = Scalar::from(1);
        assert_eq!(1, a.num_bits());
        for i in 2..Scalar::NUM_BITS {
            a = a.shl(1);
            assert_eq!(i, a.num_bits());
        }
    }

    #[test]
    fn test_scalar_legendre() {
        assert_eq!(Scalar::zero().sqrt().unwrap(), Scalar::zero());
        assert_eq!(Scalar::one().sqrt().unwrap(), Scalar::one());

        let e = Scalar::from_u64s_le(&[
            0x0dbc5349cd5664da,
            0x8ac5b6296e3ae29d,
            0x127cb819feceaa3b,
            0x3a6b21fb03867191,
        ])
        .unwrap();
        assert!(e.is_quad_res());

        let e = Scalar::from_u64s_le(&[
            0x96341aefd047c045,
            0x9b5f4254500a4d65,
            0x1ee08223b68ac240,
            0x31d9cd545c0ec7c6,
        ])
        .unwrap();
        assert!(!e.is_quad_res());
    }

    #[test]
    fn test_scalar_add_assign() {
        {
            // Random number
            let mut tmp = Scalar(blst::blst_fr {
                l: [
                    0x437ce7616d580765,
                    0xd42d1ccb29d1235b,
                    0xed8f753821bd1423,
                    0x4eede1c9c89528ca,
                ],
            });
            // assert!(tmp.is_valid());
            // Test that adding zero has no effect.
            tmp.add_assign(&Scalar(blst::blst_fr { l: [0, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x4eede1c9c89528ca
                    ]
                })
            );
            // Add one and test for the result.
            tmp.add_assign(&Scalar(blst::blst_fr { l: [1, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0x437ce7616d580766,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x4eede1c9c89528ca
                    ]
                })
            );
            // Add another random number that exercises the reduction.
            tmp.add_assign(&Scalar(blst::blst_fr {
                l: [
                    0x946f435944f7dc79,
                    0xb55e7ee6533a9b9b,
                    0x1e43b84c2f6194ca,
                    0x58717ab525463496,
                ],
            }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0xd7ec2abbb24fe3de,
                        0x35cdf7ae7d0d62f7,
                        0xd899557c477cd0e9,
                        0x3371b52bc43de018
                    ]
                })
            );
            // Add one to (r - 1) and test for the result.
            tmp = Scalar(blst::blst_fr {
                l: [
                    0xffffffff00000000,
                    0x53bda402fffe5bfe,
                    0x3339d80809a1d805,
                    0x73eda753299d7d48,
                ],
            });
            tmp.add_assign(&Scalar(blst::blst_fr { l: [1, 0, 0, 0] }));
            assert!(tmp.is_zero());
            // Add a random number to another one such that the result is r - 1
            tmp = Scalar(blst::blst_fr {
                l: [
                    0xade5adacdccb6190,
                    0xaa21ee0f27db3ccd,
                    0x2550f4704ae39086,
                    0x591d1902e7c5ba27,
                ],
            });
            tmp.add_assign(&Scalar(blst::blst_fr {
                l: [
                    0x521a525223349e70,
                    0xa99bb5f3d8231f31,
                    0xde8e397bebe477e,
                    0x1ad08e5041d7c321,
                ],
            }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0xffffffff00000000,
                        0x53bda402fffe5bfe,
                        0x3339d80809a1d805,
                        0x73eda753299d7d48
                    ]
                })
            );
            // Add one to the result and test for it.
            tmp.add_assign(&Scalar(blst::blst_fr { l: [1, 0, 0, 0] }));
            assert!(tmp.is_zero());
        }

        // Test associativity

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..1000 {
            // Generate a, b, c and ensure (a + b) + c == a + (b + c).
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let c = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);

            let mut tmp2 = b;
            tmp2.add_assign(&c);
            tmp2.add_assign(&a);

            // assert!(tmp1.is_valid());
            // assert!(tmp2.is_valid());
            assert_eq!(tmp1, tmp2, "round {}", i);
        }
    }

    #[test]
    fn test_scalar_sub_assign() {
        {
            // Test arbitrary subtraction that tests reduction.
            let mut tmp = Scalar(blst::blst_fr {
                l: [
                    0x6a68c64b6f735a2b,
                    0xd5f4d143fe0a1972,
                    0x37c17f3829267c62,
                    0xa2f37391f30915c,
                ],
            });
            tmp.sub_assign(&Scalar(blst::blst_fr {
                l: [
                    0xade5adacdccb6190,
                    0xaa21ee0f27db3ccd,
                    0x2550f4704ae39086,
                    0x591d1902e7c5ba27,
                ],
            }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0xbc83189d92a7f89c,
                        0x7f908737d62d38a3,
                        0x45aa62cfe7e4c3e1,
                        0x24ffc5896108547d
                    ]
                })
            );

            // Test the opposite subtraction which doesn't test reduction.
            tmp = Scalar(blst::blst_fr {
                l: [
                    0xade5adacdccb6190,
                    0xaa21ee0f27db3ccd,
                    0x2550f4704ae39086,
                    0x591d1902e7c5ba27,
                ],
            });
            tmp.sub_assign(&Scalar(blst::blst_fr {
                l: [
                    0x6a68c64b6f735a2b,
                    0xd5f4d143fe0a1972,
                    0x37c17f3829267c62,
                    0xa2f37391f30915c,
                ],
            }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x4eede1c9c89528ca
                    ]
                })
            );

            // Test for sensible results with zero
            tmp = Scalar(blst::blst_fr { l: [0, 0, 0, 0] });
            tmp.sub_assign(&Scalar(blst::blst_fr { l: [0, 0, 0, 0] }));
            assert!(tmp.is_zero());

            tmp = Scalar(blst::blst_fr {
                l: [
                    0x437ce7616d580765,
                    0xd42d1ccb29d1235b,
                    0xed8f753821bd1423,
                    0x4eede1c9c89528ca,
                ],
            });
            tmp.sub_assign(&Scalar(blst::blst_fr { l: [0, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Scalar(blst::blst_fr {
                    l: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x4eede1c9c89528ca
                    ]
                })
            );
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure that (a - b) + (b - a) = 0.
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1.sub_assign(&b);

            let mut tmp2 = b;
            tmp2.sub_assign(&a);

            tmp1.add_assign(&tmp2);
            assert!(tmp1.is_zero());
        }
    }

    #[test]
    fn test_scalar_mul_assign() {
        let mut tmp = Scalar(blst::blst_fr {
            l: [
                0x6b7e9b8faeefc81a,
                0xe30a8463f348ba42,
                0xeff3cb67a8279c9c,
                0x3d303651bd7c774d,
            ],
        });
        tmp.mul_assign(&Scalar(blst::blst_fr {
            l: [
                0x13ae28e3bc35ebeb,
                0xa10f4488075cae2c,
                0x8160e95a853c3b5d,
                0x5ae3f03b561a841d,
            ],
        }));
        assert!(
            tmp == Scalar(blst::blst_fr {
                l: [
                    0x23717213ce710f71,
                    0xdbee1fe53a16e1af,
                    0xf565d3e1c2a48000,
                    0x4426507ee75df9d7
                ]
            })
        );

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000000 {
            // Ensure that (a * b) * c = a * (b * c)
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let c = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1.mul_assign(&b);
            tmp1.mul_assign(&c);

            let mut tmp2 = b;
            tmp2.mul_assign(&c);
            tmp2.mul_assign(&a);

            assert_eq!(tmp1, tmp2);
        }

        for _ in 0..1000000 {
            // Ensure that r * (a + b + c) = r*a + r*b + r*c

            let r = Scalar::random(&mut rng);
            let mut a = Scalar::random(&mut rng);
            let mut b = Scalar::random(&mut rng);
            let mut c = Scalar::random(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);
            tmp1.mul_assign(&r);

            a.mul_assign(&r);
            b.mul_assign(&r);
            c.mul_assign(&r);

            a.add_assign(&b);
            a.add_assign(&c);

            assert_eq!(tmp1, a);
        }
    }

    #[test]
    fn test_scalar_squaring() {
        let a = Scalar(blst::blst_fr {
            l: [
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0x73eda753299d7d47,
            ],
        });
        // assert!(a.is_valid());
        assert_eq!(
            a.square(),
            Scalar::from_u64s_le(&[
                0xc0d698e7bde077b8,
                0xb79a310579e76ec2,
                0xac1da8d0a9af4e5f,
                0x13f629c49bf23e97
            ])
            .unwrap()
        );

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000000 {
            // Ensure that (a * a) = a^2
            let a = Scalar::random(&mut rng);

            let tmp = a.square();

            let mut tmp2 = a;
            tmp2.mul_assign(&a);

            assert_eq!(tmp, tmp2);
        }
    }

    #[test]
    fn test_scalar_inverse() {
        assert_eq!(Scalar::zero().invert().is_none().unwrap_u8(), 1);

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let one = Scalar::one();

        for i in 0..1000 {
            // Ensure that a * a^-1 = 1
            let mut a = Scalar::random(&mut rng);
            let ainv = a.invert().unwrap();
            a.mul_assign(&ainv);
            assert_eq!(a, one, "round {}", i);
        }
    }

    #[test]
    fn test_scalar_double() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure doubling a is equivalent to adding a to itself.
            let a = Scalar::random(&mut rng);
            let mut b = a;
            b.add_assign(&a);
            assert_eq!(a.double(), b);
        }
    }

    #[test]
    fn test_scalar_negate() {
        {
            let a = Scalar::zero();
            assert!((-a).is_zero());
        }

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            // Ensure (a - (-a)) = 0.
            let mut a = Scalar::random(&mut rng);
            a.add_assign(-a);
            assert!(a.is_zero());
        }
    }

    #[test]
    fn test_scalar_pow() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..1000 {
            // Exponentiate by various small numbers and ensure it consists with repeated
            // multiplication.
            let a = Scalar::random(&mut rng);
            let target = a.pow_vartime(&[i]);
            let mut c = Scalar::one();
            for _ in 0..i {
                c.mul_assign(&a);
            }
            assert_eq!(c, target);
        }

        for _ in 0..1000 {
            // Exponentiating by the modulus should have no effect in a prime field.
            let a = Scalar::random(&mut rng);

            assert_eq!(a, a.pow_vartime(&MODULUS));
        }
    }

    #[test]
    fn test_scalar_sqrt() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        assert_eq!(Scalar::zero().sqrt().unwrap(), Scalar::zero());
        assert_eq!(Scalar::one().sqrt().unwrap(), Scalar::one());

        for _ in 0..1000 {
            // Ensure sqrt(a^2) = a or -a
            let a = Scalar::random(&mut rng);
            let a_new = a.square().sqrt().unwrap();
            assert!(a_new == a || a_new == -a);
        }

        for _ in 0..1000 {
            // Ensure sqrt(a)^2 = a for random a
            let a = Scalar::random(&mut rng);
            let sqrt = a.sqrt();
            if sqrt.is_some().into() {
                assert_eq!(sqrt.unwrap().square(), a);
            }
        }
    }

    #[test]
    fn test_scalar_from_into_repr() {
        // r + 1 should not be in the field
        assert!(Scalar::from_u64s_le(&[
            0xffffffff00000002,
            0x53bda402fffe5bfe,
            0x3339d80809a1d805,
            0x73eda753299d7d48
        ])
        .is_none());

        // Modulus should not be in the field
        assert!(Scalar::from_repr(Scalar::char()).is_none());

        // Multiply some arbitrary representations to see if the result is as expected.
        let mut a = Scalar::from_u64s_le(&[
            0x25ebe3a3ad3c0c6a,
            0x6990e39d092e817c,
            0x941f900d42f5658e,
            0x44f8a103b38a71e0,
        ])
        .unwrap();
        let b = Scalar::from_u64s_le(&[
            0x264e9454885e2475,
            0x46f7746bb0308370,
            0x4683ef5347411f9,
            0x58838d7f208d4492,
        ])
        .unwrap();
        let c = Scalar::from_u64s_le(&[
            0x48a09ab93cfc740d,
            0x3a6600fbfc7a671,
            0x838567017501d767,
            0x7161d6da77745512,
        ])
        .unwrap();
        a.mul_assign(&b);
        assert_eq!(a, c);

        // Zero should be in the field.
        assert!(Scalar::from_repr([0u8; 32]).unwrap().is_zero());

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..1000 {
            // Try to turn Scalar elements into representations and back again, and compare.
            let a = Scalar::random(&mut rng);
            let a_again = Scalar::from_repr(a.to_repr()).unwrap();
            assert_eq!(a, a_again, "{}", i);
        }
    }

    #[test]
    fn test_scalar_display() {
        assert_eq!(
            format!(
                "{}",
                Scalar::from_u64s_le(&[
                    0xc3cae746a3b5ecc7,
                    0x185ec8eb3f5b5aee,
                    0x684499ffe4b9dd99,
                    0x7c9bba7afb68faa
                ])
                .unwrap()
            ),
            "Scalar(0x07c9bba7afb68faa684499ffe4b9dd99185ec8eb3f5b5aeec3cae746a3b5ecc7)"
                .to_string()
        );
        assert_eq!(
            format!(
                "{}",
                Scalar::from_u64s_le(&[
                    0x44c71298ff198106,
                    0xb0ad10817df79b6a,
                    0xd034a80a2b74132b,
                    0x41cf9a1336f50719
                ])
                .unwrap()
            ),
            "Scalar(0x41cf9a1336f50719d034a80a2b74132bb0ad10817df79b6a44c71298ff198106)"
                .to_string()
        );
    }

    #[test]
    fn test_scalar_root_of_unity() {
        assert_eq!(Scalar::S, 32);
        assert_eq!(Scalar::multiplicative_generator(), Scalar::from(7));
        assert_eq!(
            Scalar::multiplicative_generator().pow_vartime([
                0xfffe5bfeffffffff,
                0x9a1d80553bda402,
                0x299d7d483339d808,
                0x73eda753
            ]),
            Scalar::root_of_unity()
        );
        assert_eq!(
            Scalar::root_of_unity().pow_vartime([1 << Scalar::S]),
            Scalar::one()
        );
        assert!(!Scalar::multiplicative_generator().is_quad_res());
    }

    #[test]
    fn scalar_field_tests() {
        crate::tests::field::random_field_tests::<Scalar>();
        crate::tests::field::random_sqrt_tests::<Scalar>();
        crate::tests::field::from_str_tests::<Scalar>();
    }

    #[test]
    fn test_scalar_repr_conversion() {
        let a = Scalar::from(1);
        let mut expected_bytes = [0u8; 32];
        expected_bytes[0] = 1;
        assert_eq!(a, Scalar::from_repr(a.to_repr()).unwrap());
        assert_eq!(a.to_repr(), expected_bytes);
        assert_eq!(a, Scalar::from_repr(expected_bytes).unwrap());

        let a = Scalar::from(12);
        let mut expected_bytes = [0u8; 32];
        expected_bytes[0] = 12;
        assert_eq!(a, Scalar::from_repr(a.to_repr()).unwrap());
        assert_eq!(a.to_repr(), expected_bytes);
        assert_eq!(a, Scalar::from_repr(expected_bytes).unwrap());
    }
}
