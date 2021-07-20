//! An implementation of the $\mathbb{G}_2$ group of BLS12-381.

use core::{
    borrow::Borrow,
    fmt,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use blst::*;
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, CtOption};

use crate::{Bls12, Engine, Fp12, Fp2, G1Affine, Gt, PairingCurveAffine, Scalar};

/// This is an element of $\mathbb{G}_2$ represented in the affine coordinate space.
/// It is ideal to keep elements in this representation to reduce memory usage and
/// improve performance through the use of mixed curve model arithmetic.
#[derive(Copy, Clone)]
pub struct G2Affine(pub(crate) blst_p2_affine);

impl fmt::Debug for G2Affine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G2Affine")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("infinity", &self.is_zero())
            .finish()
    }
}

impl fmt::Display for G2Affine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "G2Affine(Infinity)")
        } else {
            write!(f, "G2Affine(x={}, y={})", self.x(), self.y())
        }
    }
}

impl AsRef<blst_p2_affine> for G2Affine {
    fn as_ref(&self) -> &blst_p2_affine {
        &self.0
    }
}

impl AsMut<blst_p2_affine> for G2Affine {
    fn as_mut(&mut self) -> &mut blst_p2_affine {
        &mut self.0
    }
}

impl Default for G2Affine {
    fn default() -> G2Affine {
        G2Affine::zero()
    }
}

impl From<&G2Projective> for G2Affine {
    fn from(p: &G2Projective) -> G2Affine {
        let mut out = blst_p2_affine::default();

        unsafe { blst_p2_to_affine(&mut out, &p.0) };

        G2Affine(out)
    }
}

impl From<G2Projective> for G2Affine {
    fn from(p: G2Projective) -> G2Affine {
        G2Affine::from(&p)
    }
}

impl Eq for G2Affine {}
impl PartialEq for G2Affine {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        unsafe { blst_p2_affine_is_equal(&self.0, &other.0) }
    }
}

impl Neg for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn neg(self) -> G2Projective {
        let mut out = *self;
        unsafe { blst_p2_cneg(&mut out.0, true) }
        out
    }
}

impl Neg for G2Projective {
    type Output = G2Projective;

    #[inline]
    fn neg(self) -> G2Projective {
        -&self
    }
}

impl Neg for &G2Affine {
    type Output = G2Affine;

    #[inline]
    fn neg(self) -> G2Affine {
        // Missing for affine in blst
        let mut neg = *self;
        if !self.is_zero() {
            neg.0.y = (-self.y()).0;
        }
        neg
    }
}

impl Neg for G2Affine {
    type Output = G2Affine;

    #[inline]
    fn neg(self) -> G2Affine {
        -&self
    }
}

impl Add<&G2Projective> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Projective) -> G2Projective {
        let mut out = blst_p2::default();
        unsafe { blst_p2_add_or_double(&mut out, &self.0, &rhs.0) };
        G2Projective(out)
    }
}

impl Add<&G2Affine> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Affine) -> G2Projective {
        self.add_mixed(rhs)
    }
}

impl Add<&G2Projective> for &G2Affine {
    type Output = G2Projective;

    #[inline]
    fn add(self, rhs: &G2Projective) -> G2Projective {
        rhs.add_mixed(self)
    }
}

impl Sub<&G2Projective> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Projective) -> G2Projective {
        self + -rhs
    }
}

impl Sub<&G2Projective> for &G2Affine {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Projective) -> G2Projective {
        self + -rhs
    }
}

impl Sub<&G2Affine> for &G2Projective {
    type Output = G2Projective;

    #[inline]
    fn sub(self, rhs: &G2Affine) -> G2Projective {
        self + -rhs
    }
}

impl AddAssign<&G2Projective> for G2Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G2Projective) {
        unsafe { blst_p2_add_or_double(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G2Projective> for G2Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G2Projective) {
        *self += &-rhs
    }
}

impl AddAssign<&G2Affine> for G2Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G2Affine) {
        *self = *self + rhs;
    }
}

impl SubAssign<&G2Affine> for G2Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G2Affine) {
        *self += &-rhs;
    }
}

impl Mul<&Scalar> for &G2Projective {
    type Output = G2Projective;

    fn mul(self, scalar: &Scalar) -> Self::Output {
        self.multiply(&scalar)
    }
}

impl Mul<&Scalar> for &G2Affine {
    type Output = G2Projective;

    fn mul(self, scalar: &Scalar) -> Self::Output {
        G2Projective::from(self).multiply(&scalar)
    }
}

impl MulAssign<&Scalar> for G2Projective {
    #[inline]
    fn mul_assign(&mut self, rhs: &Scalar) {
        *self = *self * rhs;
    }
}

impl MulAssign<&Scalar> for G2Affine {
    #[inline]
    fn mul_assign(&mut self, rhs: &Scalar) {
        *self = (*self * rhs).into();
    }
}

impl_add_sub!(G2Projective);
impl_add_sub!(G2Projective, G2Affine);
impl_add_sub!(G2Affine, G2Projective, G2Projective);

impl_add_sub_assign!(G2Projective);
impl_add_sub_assign!(G2Projective, G2Affine);

impl_mul!(G2Projective, Scalar);
impl_mul!(G2Affine, Scalar, G2Projective);

impl_mul_assign!(G2Projective, Scalar);
impl_mul_assign!(G2Affine, Scalar);

impl<T> Sum<T> for G2Projective
where
    T: Borrow<G2Projective>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl PrimeCurveAffine for G2Affine {
    type Scalar = Scalar;
    type Curve = G2Projective;

    fn identity() -> Self {
        G2Affine::zero()
    }

    fn generator() -> Self {
        G2Affine::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(self.is_zero() as u8)
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl ConditionallySelectable for G2Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G2Affine(blst_p2_affine {
            x: Fp2::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp2::conditional_select(&a.y(), &b.y(), choice).0,
        })
    }
}

impl ConditionallySelectable for G2Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G2Projective(blst_p2 {
            x: Fp2::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp2::conditional_select(&a.y(), &b.y(), choice).0,
            z: Fp2::conditional_select(&a.z(), &b.z(), choice).0,
        })
    }
}

impl G2Affine {
    pub fn zero() -> Self {
        G2Affine(blst_p2_affine::default())
    }

    pub fn one() -> Self {
        G2Affine(unsafe { *blst_p2_affine_generator() })
    }

    /// Determines if this point represents the point at infinity; the additive identity.
    pub fn is_zero(&self) -> bool {
        unsafe { blst_p2_affine_is_inf(&self.0) }
    }

    /// Serializes this element into compressed form.
    pub fn to_compressed(&self) -> [u8; 96] {
        let mut out = [0u8; 96];

        unsafe {
            blst_p2_affine_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    pub fn to_uncompressed(&self) -> [u8; 192] {
        let mut out = [0u8; 192];

        unsafe {
            blst_p2_affine_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    pub fn from_uncompressed(bytes: &[u8; 192]) -> CtOption<Self> {
        G2Affine::from_uncompressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_identity() | p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_uncompressed()` instead.
    pub fn from_uncompressed_unchecked(bytes: &[u8; 192]) -> CtOption<Self> {
        let mut raw = blst_p2_affine::default();
        let success =
            unsafe { blst_p2_deserialize(&mut raw, bytes.as_ptr()) != BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G2Affine(raw), Choice::from(success as u8))
    }

    /// Attempts to deserialize a compressed element.
    pub fn from_compressed(bytes: &[u8; 96]) -> CtOption<Self> {
        G2Affine::from_compressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_identity() | p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        let mut raw = blst_p2_affine::default();
        let success =
            unsafe { blst_p2_uncompress(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G2Affine(raw), Choice::from(success as u8))
    }

    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_2$. This should always return true
    /// unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        unsafe { Choice::from(blst_p2_affine_in_g2(&self.0) as u8) }
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> bool {
        // FIXME: is_zero check should happen in blst
        unsafe { blst_p2_affine_on_curve(&self.0) || self.is_zero() }
    }

    pub fn from_raw_unchecked(x: Fp2, y: Fp2, _infinity: bool) -> Self {
        // FIXME: what about infinity?
        let raw = blst_p2_affine { x: x.0, y: y.0 };

        G2Affine(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp2 {
        Fp2(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp2 {
        Fp2(self.0.y)
    }

    pub const fn uncompressed_size() -> usize {
        192
    }

    pub const fn compressed_size() -> usize {
        96
    }
}

/// This is an element of $\mathbb{G}_2$ represented in the projective coordinate space.
#[derive(Copy, Clone)]
pub struct G2Projective(pub(crate) blst_p2);

impl fmt::Debug for G2Projective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G2Projective")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("z", &self.z())
            .finish()
    }
}

impl fmt::Display for G2Projective {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", G2Affine::from(self))
    }
}

impl AsRef<blst_p2> for G2Projective {
    fn as_ref(&self) -> &blst_p2 {
        &self.0
    }
}

impl AsMut<blst_p2> for G2Projective {
    fn as_mut(&mut self) -> &mut blst_p2 {
        &mut self.0
    }
}

impl From<&G2Affine> for G2Projective {
    fn from(p: &G2Affine) -> G2Projective {
        let mut out = blst_p2::default();

        unsafe { blst_p2_from_affine(&mut out, &p.0) };

        G2Projective(out)
    }
}

impl From<G2Affine> for G2Projective {
    fn from(p: G2Affine) -> G2Projective {
        G2Projective::from(&p)
    }
}

impl Eq for G2Projective {}
impl PartialEq for G2Projective {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let self_is_zero = self.is_zero();
        let other_is_zero = other.is_zero();
        (self_is_zero && other_is_zero)
            || (!self_is_zero && !other_is_zero && unsafe { blst_p2_is_equal(&self.0, &other.0) })
    }
}

impl G2Projective {
    pub fn zero() -> Self {
        G2Projective(blst_p2::default())
    }

    pub fn one() -> Self {
        G2Projective(unsafe { *blst_p2_generator() })
    }

    pub fn is_zero(&self) -> bool {
        unsafe { blst_p2_is_inf(&self.0) }
    }

    /// Serializes this element into compressed form.
    pub fn to_compressed(&self) -> [u8; 96] {
        let mut out = [0u8; 96];

        unsafe {
            blst_p2_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    pub fn to_uncompressed(&self) -> [u8; 96] {
        let mut out = [0u8; 96];

        unsafe {
            blst_p2_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    pub fn from_uncompressed(bytes: &[u8; 192]) -> CtOption<Self> {
        G2Affine::from_uncompressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_uncompressed()` instead.
    pub fn from_uncompressed_unchecked(bytes: &[u8; 192]) -> CtOption<Self> {
        G2Affine::from_uncompressed_unchecked(bytes).map(Into::into)
    }

    /// Attempts to deserialize a compressed element.
    pub fn from_compressed(bytes: &[u8; 96]) -> CtOption<Self> {
        G2Affine::from_compressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        G2Affine::from_compressed_unchecked(bytes).map(Into::into)
    }

    /// Adds this point to another point in the affine model.
    pub fn add_mixed(&self, rhs: &G2Affine) -> G2Projective {
        let mut out = blst_p2::default();

        unsafe { blst_p2_add_or_double_affine(&mut out, &self.0, &rhs.0) };

        G2Projective(out)
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> bool {
        unsafe { blst_p2_on_curve(&self.0) }
    }

    fn multiply(&self, scalar: &Scalar) -> G2Projective {
        let mut out = blst_p2::default();

        // Sclar is 255 bits wide.
        const NBITS: usize = 255;

        unsafe { blst_p2_mult(&mut out, &self.0, scalar.to_bytes_le().as_ptr(), NBITS) };

        G2Projective(out)
    }

    pub fn from_raw_unchecked(x: Fp2, y: Fp2, z: Fp2) -> Self {
        let raw = blst_p2 {
            x: x.0,
            y: y.0,
            z: z.0,
        };

        G2Projective(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp2 {
        Fp2(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp2 {
        Fp2(self.0.y)
    }

    /// Returns the z coordinate.
    pub fn z(&self) -> Fp2 {
        Fp2(self.0.z)
    }

    /// Hash to curve algorithm.
    pub fn hash_to_curve(msg: &[u8], dst: &[u8], aug: &[u8]) -> Self {
        let mut res = Self::zero();
        unsafe {
            blst_hash_to_g2(
                &mut res.0,
                msg.as_ptr(),
                msg.len(),
                dst.as_ptr(),
                dst.len(),
                aug.as_ptr(),
                aug.len(),
            );
        }
        res
    }
}

impl Group for G2Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        let mut out = blst_p2::default();
        let mut msg = [0u8; 64];
        rng.fill_bytes(&mut msg);
        const DST: [u8; 16] = [0; 16];
        const AUG: [u8; 16] = [0; 16];

        unsafe {
            blst_encode_to_g2(
                &mut out,
                msg.as_ptr(),
                msg.len(),
                DST.as_ptr(),
                DST.len(),
                AUG.as_ptr(),
                AUG.len(),
            )
        };

        G2Projective(out)
    }

    fn identity() -> Self {
        G2Projective::zero()
    }

    fn generator() -> Self {
        G2Projective::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(self.is_zero() as u8)
    }

    fn double(&self) -> Self {
        let mut double = blst_p2::default();
        unsafe { blst_p2_double(&mut double, &self.0) };
        G2Projective(double)
    }
}

impl WnafGroup for G2Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 11] = [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl PrimeGroup for G2Projective {}

impl Curve for G2Projective {
    type AffineRepr = G2Affine;

    fn batch_normalize(proj: &[Self], affine: &mut [Self::AffineRepr]) {
        assert_eq!(proj.len(), affine.len());
        proj.iter()
            .zip(affine.iter_mut())
            .for_each(|(proj, affine)| *affine = proj.into());
    }

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G2Projective {
    type Affine = G2Affine;
}

impl GroupEncoding for G2Projective {
    type Repr = G2Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G2Compressed(self.to_compressed())
    }
}

impl GroupEncoding for G2Affine {
    type Repr = G2Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G2Compressed(self.to_compressed())
    }
}

impl UncompressedEncoding for G2Affine {
    type Uncompressed = G2Uncompressed;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed(&bytes.0)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(&bytes.0)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G2Uncompressed(self.to_uncompressed())
    }
}

#[derive(Clone, Debug)]
pub struct G2Prepared {
    pub(crate) lines: Vec<blst_fp6>,
    infinity: bool,
}

impl From<G2Affine> for G2Prepared {
    fn from(affine: G2Affine) -> Self {
        if affine.is_zero() {
            G2Prepared {
                lines: Vec::new(),
                infinity: true,
            }
        } else {
            let mut lines = vec![blst_fp6::default(); 68];
            unsafe { blst_precompute_lines(lines.as_mut_ptr(), &affine.0) }
            G2Prepared {
                lines,
                infinity: false,
            }
        }
    }
}

impl G2Prepared {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        <Bls12 as Engine>::pairing(other, self)
    }
}

#[derive(Copy, Clone)]
pub struct G2Uncompressed([u8; 192]);

encoded_point_delegations!(G2Uncompressed);

impl Default for G2Uncompressed {
    fn default() -> Self {
        G2Uncompressed([0u8; 192])
    }
}

impl fmt::Debug for G2Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

#[derive(Copy, Clone)]
pub struct G2Compressed([u8; 96]);

encoded_point_delegations!(G2Compressed);

impl Default for G2Compressed {
    fn default() -> Self {
        G2Compressed([0u8; 96])
    }
}

impl fmt::Debug for G2Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::eq_op)]

    use super::*;

    use crate::Fp;
    use ff::{Field, PrimeField};

    #[test]
    fn g2_test_is_valid() {
        // Reject point on isomorphic twist (b = 3 * (u + 1))
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xa757072d9fa35ba9,
                        0xae3fb2fb418f6e8a,
                        0xc1598ec46faa0c7c,
                        0x7a17a004747e3dbe,
                        0xcc65406a7c2e5a73,
                        0x10b8c03d64db4d0c,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xd30e70fe2f029778,
                        0xda30772df0f5212e,
                        0x5b47a9ff9a233a50,
                        0xfb777e5b9b568608,
                        0x789bac1fec71a2b9,
                        0x1342f02e2da54405,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xfe0812043de54dca,
                        0xe455171a3d47a646,
                        0xa493f36bc20be98a,
                        0x663015d9410eb608,
                        0x78e82a79d829a544,
                        0x40a00545bb3c1e,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4709802348e79377,
                        0xb5ac4dc9204bcfbd,
                        0xda361c97d02f42b2,
                        0x15008b1dc399e8df,
                        0x68128fd0548a3829,
                        0x16a613db5c873aaa,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert!(!p.is_on_curve());
        }

        // Reject point on a twist (b = 2 * (u + 1))
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xf4fdfe95a705f917,
                        0xc2914df688233238,
                        0x37c6b12cca35a34b,
                        0x41abba710d6c692c,
                        0xffcc4b2b62ce8484,
                        0x6993ec01b8934ed,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xb94e92d5f874e26,
                        0x44516408bc115d95,
                        0xe93946b290caa591,
                        0xa5a0c2b7131f3555,
                        0x83800965822367e7,
                        0x10cf1d3ad8d90bfa,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xbf00334c79701d97,
                        0x4fe714f9ff204f9a,
                        0xab70b28002f3d825,
                        0x5a9171720e73eb51,
                        0x38eb4fd8d658adb7,
                        0xb649051bbc1164d,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x9225814253d7df75,
                        0xc196c2513477f887,
                        0xe05e2fbd15a804e0,
                        0x55f2b8efad953e04,
                        0x7379345eda55265e,
                        0x377f2e6208fd4cb,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert!(!p.is_on_curve());
            assert_eq!(p.is_torsion_free().unwrap_u8(), 0);
        }

        // Reject point in an invalid subgroup
        // There is only one r-order subgroup, as r does not divide the cofactor.
        {
            let p = G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x262cea73ea1906c,
                        0x2f08540770fabd6,
                        0x4ceb92d0a76057be,
                        0x2199bc19c48c393d,
                        0x4a151b732a6075bf,
                        0x17762a3b9108c4a7,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x26f461e944bbd3d1,
                        0x298f3189a9cf6ed6,
                        0x74328ad8bc2aa150,
                        0x7e147f3f9e6e241,
                        0x72a9b63583963fff,
                        0x158b0083c000462,
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x91fb0b225ecf103b,
                        0x55d42edc1dc46ba0,
                        0x43939b11997b1943,
                        0x68cad19430706b4d,
                        0x3ccfb97b924dcea8,
                        0x1660f93434588f8d,
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xaaed3985b6dcb9c7,
                        0xc1e985d6d898d9f4,
                        0x618bd2ac3271ac42,
                        0x3940a2dbb914b529,
                        0xbeb88137cf34f3e7,
                        0x1699ee577c61b694,
                    ])
                    .unwrap(),
                ),
                false,
            );
            assert!(p.is_on_curve());
            assert_eq!(p.is_torsion_free().unwrap_u8(), 0);
        }
    }

    #[test]
    fn test_g2_addition_correctness() {
        let mut p = G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ])
                .unwrap(),
            ),
            Fp2::one(),
        );

        p.add_assign(&G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xa8c763d25910bdd3,
                    0x408777b30ca3add4,
                    0x6115fcc12e2769e,
                    0x8e73a96b329ad190,
                    0x27c546f75ee1f3ab,
                    0xa33d27add5e7e82,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x93b1ebcd54870dfe,
                    0xf1578300e1342e11,
                    0x8270dca3a912407b,
                    0x2089faf462438296,
                    0x828e5848cd48ea66,
                    0x141ecbac1deb038b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xf5d2c28857229c3f,
                    0x8c1574228757ca23,
                    0xe8d8102175f5dc19,
                    0x2767032fc37cc31d,
                    0xd5ee2aba84fd10fe,
                    0x16576ccd3dd0a4e8,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x4da9b6f6a96d1dd2,
                    0x9657f7da77f1650e,
                    0xbc150712f9ffe6da,
                    0x31898db63f87363a,
                    0xabab040ddbd097cc,
                    0x11ad236b9ba02990,
                ])
                .unwrap(),
            ),
            Fp2::one(),
        ));

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0xcde7ee8a3f2ac8af,
                        0xfc642eb35975b069,
                        0xa7de72b7dd0e64b7,
                        0xf1273e6406eef9cc,
                        0xababd760ff05cb92,
                        0xd7c20456617e89
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0xd1a50b8572cbd2b8,
                        0x238f0ac6119d07df,
                        0x4dbe924fe5fd6ac2,
                        0x8b203284c51edf6b,
                        0xc8a0b730bbb21f5e,
                        0x1a3b59d29a31274
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x9e709e78a8eaa4c9,
                        0xd30921c93ec342f4,
                        0x6d1ef332486f5e34,
                        0x64528ab3863633dc,
                        0x159384333d7cba97,
                        0x4cb84741f3cafe8
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x242af0dc3640e1a4,
                        0xe90a73ad65c66919,
                        0x2bd7ca7f4346f9ec,
                        0x38528f92b689644d,
                        0xb6884deec59fb21f,
                        0x3c075d3ec52ba90
                    ])
                    .unwrap(),
                ),
                false,
            )
        );
    }

    #[test]
    fn test_g2_doubling_correctness() {
        let mut p = G2Projective::from_raw_unchecked(
            Fp2::new(
                Fp::from_u64s_le(&[
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ])
                .unwrap(),
            ),
            Fp2::new(
                Fp::from_u64s_le(&[
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ])
                .unwrap(),
                Fp::from_u64s_le(&[
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ])
                .unwrap(),
            ),
            Fp2::one(),
        );

        p = p.double();

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine::from_raw_unchecked(
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x91ccb1292727c404,
                        0x91a6cb182438fad7,
                        0x116aee59434de902,
                        0xbcedcfce1e52d986,
                        0x9755d4a3926e9862,
                        0x18bab73760fd8024
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4e7c5e0a2ae5b99e,
                        0x96e582a27f028961,
                        0xc74d1cf4ef2d5926,
                        0xeb0cf5e610ef4fe7,
                        0x7b4c2bae8db6e70b,
                        0xf136e43909fca0
                    ])
                    .unwrap(),
                ),
                Fp2::new(
                    Fp::from_u64s_le(&[
                        0x954d4466ab13e58,
                        0x3ee42eec614cf890,
                        0x853bb1d28877577e,
                        0xa5a2a51f7fde787b,
                        0x8b92866bc6384188,
                        0x81a53fe531d64ef
                    ])
                    .unwrap(),
                    Fp::from_u64s_le(&[
                        0x4c5d607666239b34,
                        0xeddb5f48304d14b3,
                        0x337167ee6e8e3cb6,
                        0xb271f52f12ead742,
                        0x244e6c2015c83348,
                        0x19e2deae6eb9b441
                    ])
                    .unwrap(),
                ),
                false,
            )
        );
    }

    #[test]
    fn test_affine_point_equality() {
        let a = G2Affine::one();
        let b = G2Affine::zero();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn test_projective_point_equality() {
        let a = G2Projective::one();
        let b = G2Projective::zero();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn g2_curve_tests() {
        use group::tests::curve_tests;
        curve_tests::<G2Projective>();
    }

    #[test]
    fn test_g2_is_zero() {
        assert!(G2Projective::zero().is_zero());
        assert!(!G2Projective::one().is_zero());
        assert!(G2Affine::zero().is_zero());
        assert!(!G2Affine::one().is_zero());
    }
}
