mod ristretto255;

/// Scalar
pub type Scalar = ristretto255::Scalar;
/// Scalar Bytes
pub type ScalarBytes = curve25519_dalek::scalar::Scalar;

/// Generate a scalar from primitives
pub trait ScalarFromPrimitives {
  /// Convert a primitive to a scalar
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self).map(|_i| Scalar::one()).sum()
  }
}

impl ScalarFromPrimitives for bool {
  #[inline]
  fn to_scalar(self) -> Scalar {
    if self {
      Scalar::one()
    } else {
      Scalar::zero()
    }
  }
}

/// Generate scalar bytes from scalars
pub trait ScalarBytesFromScalar {
  /// Decompress Scalar
  fn decompress_scalar(s: &Scalar) -> ScalarBytes;
  /// Decompress Vector
  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes>;
}

impl ScalarBytesFromScalar for Scalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes {
    ScalarBytes::from_bytes_mod_order(s.to_bytes())
  }

  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes> {
    (0..s.len())
      .map(|i| Scalar::decompress_scalar(&s[i]))
      .collect::<Vec<ScalarBytes>>()
  }
}
