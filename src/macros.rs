// Requires the caller to manually implement `Add<&rhs, Output = output> for &lhs` and
// `Sub<&rhs, Output = output> for &lhs`.
macro_rules! impl_add_sub {
    ($t:ident) => {
        impl_add_sub!($t, $t, $t);
    };
    ($lhs:ident, $rhs:ident) => {
        impl_add_sub!($lhs, $rhs, $lhs);
    };
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl Add<&$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: &$rhs) -> $output {
                &self + rhs
            }
        }

        impl Add<$rhs> for &$lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                self + &rhs
            }
        }

        impl Add<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs) -> $output {
                &self + &rhs
            }
        }

        impl Sub<&$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: &$rhs) -> $output {
                &self - rhs
            }
        }

        impl Sub<$rhs> for &$lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                self - &rhs
            }
        }

        impl Sub<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs) -> $output {
                &self - &rhs
            }
        }
    };
}

// Requires the caller to manually implement `AddAssign<&rhs> for lhs` and
// `SubAssign<&rhs> for lhs`.
macro_rules! impl_add_sub_assign {
    ($t:ident) => {
        impl_add_sub_assign!($t, $t);
    };
    ($lhs:ident, $rhs:ident) => {
        impl AddAssign<$rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: $rhs) {
                self.add_assign(&rhs);
            }
        }

        impl SubAssign<$rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: $rhs) {
                self.sub_assign(&rhs);
            }
        }
    };
}

// Requires the caller to manually implement `Mul<&rhs, Output = output> for &lhs`.
macro_rules! impl_mul {
    ($t:ident) => {
        impl_mul!($t, $t, $t);
    };
    ($lhs:ident, $rhs:ident) => {
        impl_mul!($lhs, $rhs, $lhs);
    };
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl Mul<&$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: &$rhs) -> $output {
                &self * rhs
            }
        }

        impl Mul<$rhs> for &$lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                self * &rhs
            }
        }

        impl Mul<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                &self * &rhs
            }
        }
    };
}

// Requires the caller to manually implement `MulAssign<&rhs> for lhs`.
macro_rules! impl_mul_assign {
    ($t:ident) => {
        impl_mul_assign!($t, $t);
    };
    ($lhs:ident, $rhs:ident) => {
        impl MulAssign<$rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: $rhs) {
                self.mul_assign(&rhs);
            }
        }
    };
}

macro_rules! encoded_point_delegations {
    ($t:ident) => {
        impl AsRef<[u8]> for $t {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }
        impl AsMut<[u8]> for $t {
            fn as_mut(&mut self) -> &mut [u8] {
                &mut self.0
            }
        }

        impl PartialEq for $t {
            fn eq(&self, other: &$t) -> bool {
                PartialEq::eq(&self.0[..], &other.0[..])
            }
        }
        impl Eq for $t {}
        impl PartialOrd for $t {
            fn partial_cmp(&self, other: &$t) -> Option<::core::cmp::Ordering> {
                PartialOrd::partial_cmp(&self.0[..], &other.0[..])
            }
        }
        impl Ord for $t {
            fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
                Ord::cmp(&self.0[..], &other.0[..])
            }
        }

        impl ::core::hash::Hash for $t {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                self.0[..].hash(state);
            }
        }
    };
} // encoded_point_delegations
