use quickcheck::{Arbitrary, Gen};
use serde::de::{Error, Visitor};
use serde::{Deserializer, Serializer};
use std::fmt;

// Helper function to serialize fixed-size byte arrays
pub fn serialize_fixed_bytes<S, const N: usize>(
    bytes: &[u8; N],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_bytes(bytes)
}

// Helper function to deserialize fixed-size byte arrays
pub fn deserialize_fixed_bytes<'de, D, const N: usize>(deserializer: D) -> Result<[u8; N], D::Error>
where
    D: Deserializer<'de>,
{
    struct FixedBytesVisitor<const N: usize>;

    impl<const N: usize> Visitor<'_> for FixedBytesVisitor<N> {
        type Value = [u8; N];

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            write!(formatter, "a byte array of length {}", N)
        }

        fn visit_bytes<E>(self, v: &[u8]) -> Result<[u8; N], E>
        where
            E: Error,
        {
            if v.len() == N {
                let mut array = [0u8; N];
                array.copy_from_slice(v);
                Ok(array)
            } else {
                Err(E::invalid_length(v.len(), &self))
            }
        }
    }

    deserializer.deserialize_bytes(FixedBytesVisitor::<N>)
}

pub fn arbitrary_fixed_bytes<const N: usize>(g: &mut Gen) -> [u8; N] {
    let mut array = [0u8; N];
    for item in array.iter_mut() {
        *item = u8::arbitrary(g);
    }
    array
}
