use quickcheck::Arbitrary;
use serde::{Deserialize, Serialize};

#[derive(PartialEq, Eq, Hash, Clone, Debug, Serialize, Deserialize)]
pub struct PersistentId(pub u8);

impl Arbitrary for PersistentId {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        PersistentId(u8::arbitrary(g))
    }
}