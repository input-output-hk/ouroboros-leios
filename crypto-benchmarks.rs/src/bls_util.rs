use blst::min_sig::*;
use blst::*;
use num_bigint::{BigInt, Sign};
use num_rational::Ratio;
use num_traits::FromPrimitive;

pub fn pk_transform(f: &dyn Fn(blst_p2) -> blst_p2, pk: &PublicKey) -> PublicKey {
    let mut point: blst_p2 = blst_p2::default();
    unsafe {
        let pk_bytes: [u8; 192] = pk.serialize();
        let mut point_aff: blst_p2_affine = blst_p2_affine::default();
        blst_p2_deserialize(&mut point_aff, pk_bytes.as_ptr());
        blst_p2_from_affine(&mut point, &point_aff);
    }

    let point1: blst_p2 = f(point);

    unsafe {
        let mut point1_aff: blst_p2_affine = blst_p2_affine::default();
        blst_p2_to_affine(&mut point1_aff, &point1);
        let mut pk1_bytes: [u8; 192] = [0; 192];
        blst_p2_affine_serialize(pk1_bytes.as_mut_ptr(), &point1_aff);
        PublicKey::deserialize(&pk1_bytes).unwrap()
    }
}

pub fn sig_transform(f: &dyn Fn(blst_p1) -> blst_p1, sig: &Signature) -> Signature {
    let mut point: blst_p1 = blst_p1::default();
    unsafe {
        let sig_bytes: [u8; 96] = sig.serialize();
        let mut point_aff: blst_p1_affine = blst_p1_affine::default();
        blst_p1_deserialize(&mut point_aff, sig_bytes.as_ptr());
        blst_p1_from_affine(&mut point, &point_aff);
    }

    let point1: blst_p1 = f(point);

    unsafe {
        let mut point1_aff: blst_p1_affine = blst_p1_affine::default();
        blst_p1_to_affine(&mut point1_aff, &point1);
        let mut sig1_bytes: [u8; 96] = [0; 96];
        blst_p1_affine_serialize(sig1_bytes.as_mut_ptr(), &point1_aff);
        Signature::deserialize(&sig1_bytes).unwrap()
    }
}

pub fn sig_to_rational(sig: &Signature) -> Ratio<BigInt> {
    let bytes: [u8; 48] = sig.to_bytes();
    let numer = BigInt::from_bytes_be(Sign::Plus, &bytes);
    let denom: BigInt = BigInt::from_u128(2u128 ^ 127u128).unwrap();
    Ratio::new(numer % denom.clone(), denom)
}
