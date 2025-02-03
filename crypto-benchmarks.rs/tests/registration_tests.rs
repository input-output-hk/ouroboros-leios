#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use leios_crypto_benchmarks::registration::Registration;

#[quickcheck]
    fn registration_size(reg: Registration) -> () {
      let expected = 668 + 3; // Includes CBOR overhead for bytes.
      let bytes = serde_cbor::to_vec(&reg).expect("Failed to serialize registration.");
      let actual = bytes.len();
      assert_eq!(expected, actual, "Expected {} bytes but got {}", expected, actual);
    }
