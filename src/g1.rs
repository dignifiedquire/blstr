//! An implementation of the $\mathbb{G}_1$ group of BLS12-381.

use core::{
    borrow::Borrow,
    fmt,
    iter::Sum,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::io::Read;

use blst::*;
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, CtOption};

use crate::{Bls12, Engine, Fp, Fp12, G2Affine, Gt, PairingCurveAffine, Scalar};

/// This is an element of $\mathbb{G}_1$ represented in the affine coordinate space.
/// It is ideal to keep elements in this representation to reduce memory usage and
/// improve performance through the use of mixed curve model arithmetic.
#[derive(Copy, Clone)]
pub struct G1Affine(pub(crate) blst_p1_affine);

impl fmt::Debug for G1Affine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G1Affine")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("infinity", &self.is_zero())
            .finish()
    }
}

impl fmt::Display for G1Affine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "G1Affine(Infinity)")
        } else {
            write!(f, "G1Affine(x={}, y={})", self.x(), self.y())
        }
    }
}

impl Default for G1Affine {
    fn default() -> G1Affine {
        G1Affine::identity()
    }
}

impl From<&G1Projective> for G1Affine {
    fn from(p: &G1Projective) -> G1Affine {
        let mut out = blst_p1_affine::default();

        unsafe { blst_p1_to_affine(&mut out, &p.0) };

        G1Affine(out)
    }
}

impl From<G1Projective> for G1Affine {
    fn from(p: G1Projective) -> G1Affine {
        G1Affine::from(&p)
    }
}

impl AsRef<blst_p1_affine> for G1Affine {
    fn as_ref(&self) -> &blst_p1_affine {
        &self.0
    }
}

impl AsMut<blst_p1_affine> for G1Affine {
    fn as_mut(&mut self) -> &mut blst_p1_affine {
        &mut self.0
    }
}

impl Eq for G1Affine {}
impl PartialEq for G1Affine {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        unsafe { blst_p1_affine_is_equal(&self.0, &other.0) }
    }
}

impl Neg for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn neg(self) -> G1Projective {
        let mut neg = *self;
        unsafe { blst_p1_cneg(&mut neg.0, true) };
        neg
    }
}

impl Neg for G1Projective {
    type Output = G1Projective;

    #[inline]
    fn neg(self) -> G1Projective {
        -&self
    }
}

impl Neg for &G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(self) -> G1Affine {
        // Missing for affine in blst
        let mut neg = *self;
        if !self.is_zero() {
            neg.0.y = (-self.y()).0;
        }
        neg
    }
}

impl Neg for G1Affine {
    type Output = G1Affine;

    #[inline]
    fn neg(self) -> G1Affine {
        -&self
    }
}

impl Add<&G1Projective> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Projective) -> G1Projective {
        let mut out = blst_p1::default();
        unsafe { blst_p1_add_or_double(&mut out, &self.0, &rhs.0) };
        G1Projective(out)
    }
}

impl Add<&G1Projective> for &G1Affine {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Projective) -> G1Projective {
        rhs.add_mixed(self)
    }
}

impl Add<&G1Affine> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn add(self, rhs: &G1Affine) -> G1Projective {
        self.add_mixed(rhs)
    }
}

impl Sub<&G1Projective> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Projective) -> G1Projective {
        self + (-rhs)
    }
}

impl Sub<&G1Projective> for &G1Affine {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Projective) -> G1Projective {
        self + (-rhs)
    }
}

impl Sub<&G1Affine> for &G1Projective {
    type Output = G1Projective;

    #[inline]
    fn sub(self, rhs: &G1Affine) -> G1Projective {
        self + (-rhs)
    }
}

impl AddAssign<&G1Projective> for G1Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G1Projective) {
        unsafe { blst_p1_add_or_double(&mut self.0, &self.0, &rhs.0) };
    }
}

impl SubAssign<&G1Projective> for G1Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G1Projective) {
        *self += &-rhs;
    }
}

impl AddAssign<&G1Affine> for G1Projective {
    #[inline]
    fn add_assign(&mut self, rhs: &G1Affine) {
        *self = *self + rhs;
    }
}

impl SubAssign<&G1Affine> for G1Projective {
    #[inline]
    fn sub_assign(&mut self, rhs: &G1Affine) {
        *self += &-rhs;
    }
}

impl Mul<&Scalar> for &G1Projective {
    type Output = G1Projective;

    fn mul(self, scalar: &Scalar) -> Self::Output {
        self.multiply(&scalar)
    }
}

impl Mul<&Scalar> for &G1Affine {
    type Output = G1Projective;

    fn mul(self, scalar: &Scalar) -> Self::Output {
        G1Projective::from(self).multiply(&scalar)
    }
}

impl MulAssign<&Scalar> for G1Projective {
    #[inline]
    fn mul_assign(&mut self, rhs: &Scalar) {
        *self = *self * rhs;
    }
}

impl MulAssign<&Scalar> for G1Affine {
    #[inline]
    fn mul_assign(&mut self, rhs: &Scalar) {
        *self = (*self * rhs).into();
    }
}

impl_add_sub!(G1Projective);
impl_add_sub!(G1Projective, G1Affine);
impl_add_sub!(G1Affine, G1Projective, G1Projective);

impl_add_sub_assign!(G1Projective);
impl_add_sub_assign!(G1Projective, G1Affine);

impl_mul!(G1Projective, Scalar);
impl_mul!(G1Affine, Scalar, G1Projective);

impl_mul_assign!(G1Projective, Scalar);
impl_mul_assign!(G1Affine, Scalar);

impl<T> Sum<T> for G1Projective
where
    T: Borrow<G1Projective>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl ConditionallySelectable for G1Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Affine(blst_p1_affine {
            x: Fp::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp::conditional_select(&a.y(), &b.y(), choice).0,
        })
    }
}

impl ConditionallySelectable for G1Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Projective(blst_p1 {
            x: Fp::conditional_select(&a.x(), &b.x(), choice).0,
            y: Fp::conditional_select(&a.y(), &b.y(), choice).0,
            z: Fp::conditional_select(&a.z(), &b.z(), choice).0,
        })
    }
}

impl G1Affine {
    pub fn zero() -> Self {
        G1Affine(blst_p1_affine::default())
    }

    pub fn one() -> Self {
        G1Affine(unsafe { *blst_p1_affine_generator() })
    }

    pub fn is_zero(&self) -> bool {
        unsafe { blst_p1_affine_is_inf(&self.0) }
    }

    /// Serializes this element into compressed form.
    pub fn to_compressed(&self) -> [u8; 48] {
        let mut out = [0u8; 48];

        unsafe {
            blst_p1_affine_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    pub fn to_uncompressed(&self) -> [u8; 96] {
        let mut out = [0u8; 96];

        unsafe {
            blst_p1_affine_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    pub fn from_uncompressed(bytes: &[u8; 96]) -> CtOption<Self> {
        G1Affine::from_uncompressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_identity() | p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_uncompressed()` instead.
    pub fn from_uncompressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        let mut raw = blst_p1_affine::default();
        let success =
            unsafe { blst_p1_deserialize(&mut raw, bytes.as_ptr()) != BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G1Affine(raw), Choice::from(success as u8))
    }

    /// Attempts to deserialize a compressed element.
    pub fn from_compressed(bytes: &[u8; 48]) -> CtOption<Self> {
        G1Affine::from_compressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_identity() | p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 48]) -> CtOption<Self> {
        let mut raw = blst_p1_affine::default();
        let success =
            unsafe { blst_p1_uncompress(&mut raw, bytes.as_ptr()) == BLST_ERROR::BLST_SUCCESS };
        CtOption::new(G1Affine(raw), Choice::from(success as u8))
    }

    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_1$. This should always return true
    /// unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        unsafe { Choice::from(blst_p1_affine_in_g1(&self.0) as u8) }
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> bool {
        unsafe { blst_p1_affine_on_curve(&self.0) || self.is_zero() }
    }

    pub fn from_raw_unchecked(x: Fp, y: Fp, _infinity: bool) -> Self {
        // FIXME: what about infinity?
        let raw = blst_p1_affine { x: x.0, y: y.0 };

        G1Affine(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp {
        Fp(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp {
        Fp(self.0.y)
    }

    pub const fn uncompressed_size() -> usize {
        96
    }

    pub const fn compressed_size() -> usize {
        48
    }

    #[inline]
    pub fn raw_fmt_size() -> usize {
        let s = G1Affine::uncompressed_size();
        s + 1
    }

    pub fn write_raw<W: std::io::Write>(&self, mut writer: W) -> Result<usize, std::io::Error> {
        if self.is_zero() {
            writer.write_all(&[1])?;
        } else {
            writer.write_all(&[0])?;
        }
        let raw = self.to_uncompressed();
        writer.write_all(&raw)?;

        Ok(Self::raw_fmt_size())
    }

    pub fn read_raw<R: Read>(mut reader: R) -> Result<Self, std::io::Error> {
        let mut buf = [0u8];
        reader.read_exact(&mut buf)?;
        let _infinity = buf[0] == 1;

        let mut buf = [0u8; 96];
        reader.read_exact(&mut buf)?;
        let res = Self::from_uncompressed_unchecked(&buf);
        if res.is_some().into() {
            Ok(res.unwrap())
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "not on curve",
            ))
        }
    }

    pub fn read_raw_checked<R: Read>(mut reader: R) -> Result<Self, std::io::Error> {
        let mut buf = [0u8];
        reader.read_exact(&mut buf)?;
        let _infinity = buf[0] == 1;

        let mut buf = [0u8; 96];
        reader.read_exact(&mut buf)?;
        let res = Self::from_uncompressed(&buf);
        if res.is_some().into() {
            Ok(res.unwrap())
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "not on curve",
            ))
        }
    }
}

/// This is an element of $\mathbb{G}_1$ represented in the projective coordinate space.
#[derive(Copy, Clone)]
pub struct G1Projective(pub(crate) blst_p1);

impl fmt::Debug for G1Projective {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("G1Projective")
            .field("x", &self.x())
            .field("y", &self.y())
            .field("z", &self.z())
            .finish()
    }
}

impl fmt::Display for G1Projective {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", G1Affine::from(self))
    }
}

impl AsRef<blst_p1> for G1Projective {
    fn as_ref(&self) -> &blst_p1 {
        &self.0
    }
}

impl AsMut<blst_p1> for G1Projective {
    fn as_mut(&mut self) -> &mut blst_p1 {
        &mut self.0
    }
}

impl From<&G1Affine> for G1Projective {
    fn from(p: &G1Affine) -> G1Projective {
        let mut out = blst_p1::default();

        unsafe { blst_p1_from_affine(&mut out, &p.0) };

        G1Projective(out)
    }
}

impl From<G1Affine> for G1Projective {
    fn from(p: G1Affine) -> G1Projective {
        G1Projective::from(&p)
    }
}

impl Eq for G1Projective {}
impl PartialEq for G1Projective {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let self_is_zero = self.is_zero();
        let other_is_zero = other.is_zero();
        (self_is_zero && other_is_zero)
            || (!self_is_zero && !other_is_zero && unsafe { blst_p1_is_equal(&self.0, &other.0) })
    }
}

impl G1Projective {
    pub fn zero() -> Self {
        G1Projective(blst_p1::default())
    }

    pub fn one() -> Self {
        G1Projective(unsafe { *blst_p1_generator() })
    }

    pub fn is_zero(&self) -> bool {
        unsafe { blst_p1_is_inf(&self.0) }
    }

    /// Serializes this element into compressed form.
    pub fn to_compressed(&self) -> [u8; 48] {
        let mut out = [0u8; 48];

        unsafe {
            blst_p1_compress(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Serializes this element into uncompressed form.
    pub fn to_uncompressed(&self) -> [u8; 96] {
        let mut out = [0u8; 96];

        unsafe {
            blst_p1_serialize(out.as_mut_ptr(), &self.0);
        }

        out
    }

    /// Attempts to deserialize an uncompressed element.
    pub fn from_uncompressed(bytes: &[u8; 96]) -> CtOption<Self> {
        G1Affine::from_uncompressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_uncompressed()` instead.
    pub fn from_uncompressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        G1Affine::from_uncompressed_unchecked(bytes).map(Into::into)
    }

    /// Attempts to deserialize a compressed element.
    pub fn from_compressed(bytes: &[u8; 48]) -> CtOption<Self> {
        G1Affine::from_compressed(bytes).map(Into::into)
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    ///
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 48]) -> CtOption<Self> {
        G1Affine::from_compressed_unchecked(bytes).map(Into::into)
    }

    /// Adds this point to another point in the affine model.
    fn add_mixed(&self, rhs: &G1Affine) -> G1Projective {
        let mut out = blst_p1::default();

        unsafe { blst_p1_add_or_double_affine(&mut out, &self.0, &rhs.0) };

        G1Projective(out)
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> bool {
        unsafe { blst_p1_on_curve(&self.0) }
    }

    fn multiply(&self, scalar: &Scalar) -> G1Projective {
        let mut out = blst_p1::default();

        // Scalar is 255 bits wide.
        const NBITS: usize = 255;

        unsafe { blst_p1_mult(&mut out, &self.0, scalar.to_bytes_le().as_ptr(), NBITS) };

        G1Projective(out)
    }

    pub fn from_raw_unchecked(x: Fp, y: Fp, z: Fp) -> Self {
        let raw = blst_p1 {
            x: x.0,
            y: y.0,
            z: z.0,
        };

        G1Projective(raw)
    }

    /// Returns the x coordinate.
    pub fn x(&self) -> Fp {
        Fp(self.0.x)
    }

    /// Returns the y coordinate.
    pub fn y(&self) -> Fp {
        Fp(self.0.y)
    }

    /// Returns the z coordinate.
    pub fn z(&self) -> Fp {
        Fp(self.0.z)
    }

    /// Hash to curve algorithm.
    pub fn hash_to_curve(msg: &[u8], dst: &[u8], aug: &[u8]) -> Self {
        let mut res = Self::identity();
        unsafe {
            blst_hash_to_g1(
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

impl Group for G1Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        let mut out = blst_p1::default();
        let mut msg = [0u8; 64];
        rng.fill_bytes(&mut msg);
        const DST: [u8; 16] = [0; 16];
        const AUG: [u8; 16] = [0; 16];

        unsafe {
            blst_encode_to_g1(
                &mut out,
                msg.as_ptr(),
                msg.len(),
                DST.as_ptr(),
                DST.len(),
                AUG.as_ptr(),
                AUG.len(),
            )
        };

        G1Projective(out)
    }

    fn identity() -> Self {
        G1Projective::zero()
    }

    fn generator() -> Self {
        G1Projective::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(self.is_zero() as u8)
    }

    fn double(&self) -> Self {
        let mut double = blst_p1::default();
        unsafe { blst_p1_double(&mut double, &self.0) };
        G1Projective(double)
    }
}

impl WnafGroup for G1Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

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

impl PrimeGroup for G1Projective {}

impl Curve for G1Projective {
    type AffineRepr = G1Affine;

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

impl PrimeCurve for G1Projective {
    type Affine = G1Affine;
}

impl PrimeCurveAffine for G1Affine {
    type Scalar = Scalar;
    type Curve = G1Projective;

    fn identity() -> Self {
        G1Affine::zero()
    }

    fn generator() -> Self {
        G1Affine::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(self.is_zero() as u8)
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl GroupEncoding for G1Projective {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Compressed(self.to_compressed())
    }
}

impl GroupEncoding for G1Affine {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Compressed(self.to_compressed())
    }
}

impl UncompressedEncoding for G1Affine {
    type Uncompressed = G1Uncompressed;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed(&bytes.0)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(&bytes.0)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G1Uncompressed(self.to_uncompressed())
    }
}

#[derive(Copy, Clone)]
pub struct G1Uncompressed([u8; 96]);

encoded_point_delegations!(G1Uncompressed);

impl Default for G1Uncompressed {
    fn default() -> Self {
        G1Uncompressed([0u8; 96])
    }
}

impl fmt::Debug for G1Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

#[derive(Copy, Clone)]
pub struct G1Compressed([u8; 48]);

encoded_point_delegations!(G1Compressed);

impl Default for G1Compressed {
    fn default() -> Self {
        G1Compressed([0u8; 48])
    }
}

impl fmt::Debug for G1Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        <Bls12 as Engine>::pairing(self, other)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::eq_op)]

    use super::*;

    use ff::Field;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn curve_tests() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Negation edge case with zero.
        {
            let mut z = G1Projective::zero();
            z = z.neg();
            assert!(z.is_zero());
        }

        // Doubling edge case with zero.
        {
            let mut z = G1Projective::zero();
            z = z.double();
            assert!(z.is_zero());
        }

        // Addition edge cases with zero
        {
            let mut r = G1Projective::random(&mut rng);
            let rcopy = r;
            r += &G1Projective::zero();
            assert_eq!(r, rcopy);
            r += &G1Affine::zero();
            assert_eq!(r, rcopy);

            let mut z = G1Projective::zero();
            z += &G1Projective::zero();
            assert!(z.is_zero());
            z += &G1Affine::zero();
            assert!(z.is_zero());

            let mut z2 = z;
            z2 += &r;

            z += &G1Affine::from(r);

            assert_eq!(z, z2);
            assert_eq!(z, r);
        }

        // Transformations
        {
            let a = G1Projective::random(&mut rng);
            let b: G1Projective = G1Affine::from(a).into();
            let c = G1Projective::from(G1Affine::from(G1Projective::from(G1Affine::from(a))));

            assert_eq!(a, b);
            assert_eq!(b, c);
        }
    }

    #[test]
    fn test_is_on_curve() {
        assert!(G1Projective::zero().is_on_curve());
        assert!(G1Projective::one().is_on_curve());

        assert!(G1Affine::zero().is_on_curve());
        assert!(G1Affine::one().is_on_curve());

        let z = Fp::from_raw_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let gen = G1Affine::one();
        let z2 = z.square();
        let mut test = G1Projective::from_raw_unchecked(gen.x() * z2, gen.y() * (z2 * z), z);

        assert!(test.is_on_curve());

        test.0.x = z.0;
        assert!(!test.is_on_curve());
    }

    #[test]
    fn test_affine_point_equality() {
        let a = G1Affine::one();
        let b = G1Affine::zero();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);
    }

    #[test]
    fn test_projective_point_equality() {
        let a = G1Projective::one();
        let b = G1Projective::zero();

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
        assert_ne!(b, a);

        let z = Fp::from_raw_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let z2 = z.square();
        let mut c = G1Projective::from_raw_unchecked(a.x() * z2, a.y() * (z2 * z), z);
        assert!(c.is_on_curve());

        assert_eq!(a, c);
        assert_eq!(c, a);
        assert_ne!(b, c);
        assert_ne!(c, b);

        c.0.y = (-c.y()).0;
        assert!(c.is_on_curve());

        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(c, a);
        assert_ne!(c, b);

        c.0.y = (-c.y()).0;
        c.0.x = z.0;
        assert!(!c.is_on_curve());
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
    }

    #[test]
    fn test_projective_to_affine() {
        let a = G1Projective::one();
        let b = G1Projective::zero();

        assert!(G1Affine::from(a).is_on_curve());
        assert!(!G1Affine::from(a).is_zero());
        assert!(G1Affine::from(b).is_on_curve());
        assert!(G1Affine::from(b).is_zero());

        let z = Fp::from_raw_unchecked([
            0xba7afa1f9a6fe250,
            0xfa0f5b595eafe731,
            0x3bdc477694c306e7,
            0x2149be4b3949fa24,
            0x64aa6e0649b2078c,
            0x12b108ac33643c3e,
        ]);

        let z2 = z.square();
        let c = G1Projective::from_raw_unchecked(a.x() * z2, a.y() * (z2 * z), z);

        assert_eq!(G1Affine::from(c), G1Affine::one());
    }

    #[test]
    fn test_affine_to_projective() {
        let a = G1Affine::one();
        let b = G1Affine::zero();

        assert!(G1Projective::from(a).is_on_curve());
        assert!(!G1Projective::from(a).is_zero());
        assert!(G1Projective::from(b).is_on_curve());
        assert!(G1Projective::from(b).is_zero());
    }

    #[test]
    fn test_doubling() {
        {
            let tmp = G1Projective::zero().double();
            assert!(tmp.is_zero());
            assert!(tmp.is_on_curve());
        }
        {
            let tmp = G1Projective::one().double();
            assert!(!tmp.is_zero());
            assert!(tmp.is_on_curve());

            assert_eq!(
                G1Affine::from(tmp),
                G1Affine::from_raw_unchecked(
                    Fp::from_raw_unchecked([
                        0x53e978ce58a9ba3c,
                        0x3ea0583c4f3d65f9,
                        0x4d20bb47f0012960,
                        0xa54c664ae5b2b5d9,
                        0x26b552a39d7eb21f,
                        0x8895d26e68785
                    ]),
                    Fp::from_raw_unchecked([
                        0x70110b3298293940,
                        0xda33c5393f1f6afc,
                        0xb86edfd16a5aa785,
                        0xaec6d1c9e7b1c895,
                        0x25cfc2b522d11720,
                        0x6361c83f8d09b15
                    ]),
                    false
                )
            );
        }
    }

    #[test]
    fn test_projective_addition() {
        {
            let a = G1Projective::zero();
            let b = G1Projective::zero();
            let c = a + b;
            assert!(c.is_zero());
            assert!(c.is_on_curve());
        }
        {
            let a = G1Projective::zero();
            let mut b = G1Projective::one();
            {
                let z = Fp::from_raw_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = a + b;
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert_eq!(c, G1Projective::one());
        }
        {
            let a = G1Projective::zero();
            let mut b = G1Projective::one();
            {
                let z = Fp::from_raw_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = b + a;
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert_eq!(c, G1Projective::one());
        }
        {
            let a = G1Projective::one().double().double(); // 4P
            let b = G1Projective::one().double(); // 2P
            let c = a + b;

            let mut d = G1Projective::one();
            for _ in 0..5 {
                d += G1Projective::one();
            }
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert!(!d.is_zero());
            assert!(d.is_on_curve());
            assert_eq!(c, d);
        }

        // Degenerate case
        {
            let mut beta = Fp::from_raw_unchecked([
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ]);
            beta = beta.square();
            let a = G1Projective::one().double().double();
            let b = G1Projective::from_raw_unchecked(a.x() * beta, -a.y(), a.z());
            assert!(a.is_on_curve());
            assert!(b.is_on_curve());

            let c = a + b;
            assert_eq!(
                G1Affine::from(c),
                G1Affine::from(G1Projective::from_raw_unchecked(
                    Fp::from_raw_unchecked([
                        0x29e1e987ef68f2d0,
                        0xc5f3ec531db03233,
                        0xacd6c4b6ca19730f,
                        0x18ad9e827bc2bab7,
                        0x46e3b2c5785cc7a9,
                        0x7e571d42d22ddd6
                    ]),
                    Fp::from_raw_unchecked([
                        0x94d117a7e5a539e7,
                        0x8e17ef673d4b5d22,
                        0x9d746aaf508a33ea,
                        0x8c6d883d2516c9a2,
                        0xbc3b8d5fb0447f7,
                        0x7bfa4c7210f4f44
                    ]),
                    Fp::one(),
                ))
            );
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
        }
    }

    #[test]
    fn test_mixed_addition() {
        {
            let a = G1Affine::zero();
            let b = G1Projective::zero();
            let c = a + b;
            assert!(c.is_zero());
            assert!(c.is_on_curve());
        }
        {
            let a = G1Affine::zero();
            let mut b = G1Projective::one();
            {
                let z = Fp::from_raw_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = a + b;
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert_eq!(c, G1Projective::one());
        }
        {
            let a = G1Affine::zero();
            let mut b = G1Projective::one();
            {
                let z = Fp::from_raw_unchecked([
                    0xba7afa1f9a6fe250,
                    0xfa0f5b595eafe731,
                    0x3bdc477694c306e7,
                    0x2149be4b3949fa24,
                    0x64aa6e0649b2078c,
                    0x12b108ac33643c3e,
                ]);

                let z2 = z.square();
                b = G1Projective::from_raw_unchecked(b.x() * (z2), b.y() * (z2 * z), z);
            }
            let c = b + a;
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert_eq!(c, G1Projective::one());
        }
        {
            let a = G1Projective::one().double().double(); // 4P
            let b = G1Projective::one().double(); // 2P
            let c = a + b;

            let mut d = G1Projective::one();
            for _ in 0..5 {
                d += G1Affine::one();
            }
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
            assert!(!d.is_zero());
            assert!(d.is_on_curve());
            assert_eq!(c, d);
        }

        // Degenerate case
        {
            let mut beta = Fp::from_raw_unchecked([
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x3f97d6e83d050d2,
                0x18f0206554638741,
            ]);
            beta = beta.square();
            let a = G1Projective::one().double().double();
            let b = G1Projective::from_raw_unchecked(a.x() * beta, -a.y(), a.z());
            let a = G1Affine::from(a);
            assert!(a.is_on_curve());
            assert!(b.is_on_curve());

            let c = a + b;
            assert_eq!(
                G1Affine::from(c),
                G1Affine::from(G1Projective::from_raw_unchecked(
                    Fp::from_raw_unchecked([
                        0x29e1e987ef68f2d0,
                        0xc5f3ec531db03233,
                        0xacd6c4b6ca19730f,
                        0x18ad9e827bc2bab7,
                        0x46e3b2c5785cc7a9,
                        0x7e571d42d22ddd6
                    ]),
                    Fp::from_raw_unchecked([
                        0x94d117a7e5a539e7,
                        0x8e17ef673d4b5d22,
                        0x9d746aaf508a33ea,
                        0x8c6d883d2516c9a2,
                        0xbc3b8d5fb0447f7,
                        0x7bfa4c7210f4f44
                    ]),
                    Fp::one()
                ))
            );
            assert!(!c.is_zero());
            assert!(c.is_on_curve());
        }
    }

    #[test]
    fn test_projective_negation_and_subtraction() {
        let a = G1Projective::one().double();
        assert_eq!(a + (-a), G1Projective::zero());
        assert_eq!(a + (-a), a - a);
    }

    #[test]
    fn test_affine_negation_and_subtraction() {
        let a = G1Affine::one();
        assert_eq!(G1Projective::from(a) + (-a), G1Projective::zero());
        assert_eq!(G1Projective::from(a) + (-a), G1Projective::from(a) - a);
    }

    #[test]
    fn test_projective_scalar_multiplication() {
        let g = G1Projective::one();
        let a = Scalar(blst::blst_fr {
            l: [
                0x2b568297a56da71c,
                0xd8c39ecb0ef375d1,
                0x435c38da67bfbf96,
                0x8088a05026b659b2,
            ],
        });
        let b = Scalar(blst_fr {
            l: [
                0x785fdd9b26ef8b85,
                0xc997f25837695c18,
                0x4c8dbc39e7b756c1,
                0x70d9b6cc6d87df20,
            ],
        });
        let c = a * b;

        assert_eq!((g * a) * b, g * c);
    }

    #[test]
    fn test_affine_scalar_multiplication() {
        let g = G1Affine::one();
        let a = Scalar(blst::blst_fr {
            l: [
                0x2b568297a56da71c,
                0xd8c39ecb0ef375d1,
                0x435c38da67bfbf96,
                0x8088a05026b659b2,
            ],
        });
        let b = Scalar(blst::blst_fr {
            l: [
                0x785fdd9b26ef8b85,
                0xc997f25837695c18,
                0x4c8dbc39e7b756c1,
                0x70d9b6cc6d87df20,
            ],
        });
        let c = a * b;

        assert_eq!(G1Affine::from(g * a) * b, g * c);
    }

    #[test]
    fn g1_curve_tests() {
        use group::tests::curve_tests;
        curve_tests::<G1Projective>();
    }

    #[test]
    fn test_g1_is_zero() {
        assert!(G1Projective::zero().is_zero());
        assert!(!G1Projective::one().is_zero());
        assert!(G1Affine::zero().is_zero());
        assert!(!G1Affine::one().is_zero());
    }
}
