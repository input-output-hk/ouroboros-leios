use blst::*;
use min_pk::SecretKey;
use rand::RngCore;

pub fn sk_random() -> SecretKey {
    let mut rng = rand::thread_rng();
    let mut ikm = [0u8; 32];
    rng.fill_bytes(&mut ikm);
    SecretKey::key_gen(&ikm, &[]).unwrap()
}

fn sk_scalar(sk: &SecretKey) -> blst_scalar {
    let ser = sk.serialize();
    let mut sk1: blst_scalar = blst_scalar::default();
    unsafe {
        blst_scalar_from_bendian(&mut sk1, ser.as_ptr());
    }
    sk1
}

pub fn sk_to_pk_point(sk: &SecretKey) -> blst_p1 {
    let sk_sca: blst_scalar = sk_scalar(sk);
    let mut pk: blst_p1 = blst_p1::default();
    unsafe {
        blst_sk_to_pk_in_g1(&mut pk, &sk_sca);
    }
    pk
}

fn rnd_scalar() -> blst_scalar {
    let mut rng = rand::thread_rng();
    let mut scalar_bytes: [u8; 32] = [0u8; 32];
    rng.fill_bytes(&mut scalar_bytes);
    let mut scalar: blst_scalar = blst_scalar::default();
    unsafe {
        blst::blst_scalar_from_lendian(&mut scalar, scalar_bytes.as_ptr());
    }
    scalar
}

pub fn vrf_prove(sk: &SecretKey, input: &[u8], dst: &[u8]) -> (blst_p1, blst_scalar, blst_fr) {
    let sk_bytes: [u8; 32] = sk.to_bytes();

    let aug = [];

    let mut hh: blst::blst_p1 = blst::blst_p1::default();
    let hh_ptr: *const blst::blst_p1 = &hh;
    unsafe {
        blst_hash_to_g1(
            &mut hh,
            input.as_ptr(),
            input.len(),
            dst.as_ptr(),
            dst.len(),
            aug.as_ptr(),
            aug.len(),
        );
    }

    let mut gamma: blst_p1 = blst_p1::default();
    unsafe {
        blst_p1_mult(&mut gamma, hh_ptr, sk_bytes.as_ptr(), sk_bytes.len());
    }

    let k: blst_scalar = rnd_scalar();
    let k_ptr: *const u8 = k.b.as_ptr();
    let k_len: usize = 8 * k.b.len();

    let mut uu = blst_p1::default();
    let mut vv: blst_p1 = blst_p1::default();
    unsafe {
        blst_p1_mult(&mut uu, blst_p1_generator(), k_ptr, k_len);
        blst_p1_mult(&mut vv, hh_ptr, k_ptr, k_len);
    }
    let mut bytes64: [u64; 3 * 3 * 6] = [0; 3 * 3 * 6];
    bytes64[0..6].copy_from_slice(&gamma.x.l);
    bytes64[6..12].copy_from_slice(&gamma.y.l);
    bytes64[12..18].copy_from_slice(&gamma.z.l);
    bytes64[18..24].copy_from_slice(&uu.x.l);
    bytes64[24..30].copy_from_slice(&uu.y.l);
    bytes64[30..36].copy_from_slice(&uu.z.l);
    bytes64[36..42].copy_from_slice(&vv.x.l);
    bytes64[42..48].copy_from_slice(&vv.y.l);
    bytes64[48..54].copy_from_slice(&vv.z.l);
    let bytes8: [u8; 432] = unsafe { std::mem::transmute(bytes64) };
    let mut c_bytes: [u8; 32] = [0; 32];
    let mut c = blst_scalar::default();
    unsafe {
        blst_sha256(c_bytes.as_mut_ptr(), bytes8.as_ptr(), bytes8.len());
        blst_scalar_from_bendian(&mut c, c_bytes.as_ptr());
    }

    let mut s: blst_fr = blst_fr::default();
    unsafe {
        let sk_sca = sk_scalar(sk);
        let mut sk_fr: blst_fr = blst_fr::default();
        blst_fr_from_scalar(&mut sk_fr, &sk_sca);
        let mut csk: blst_fr = blst_fr::default();
        blst_fr_mul(&mut csk, &csk, &sk_fr);
        let mut k_fr: blst_fr = blst_fr::default();
        blst_fr_from_scalar(&mut k_fr, &k);
        blst_fr_add(&mut s, &k_fr, &csk);
    }

    (gamma, c, s)
}

pub fn vrf_verify(
    pk: &blst_p1,
    input: &[u8],
    dst: &[u8],
    gamma: &blst_p1,
    c: &blst_scalar,
    s: &blst_fr,
) -> bool {
    let aug = [];

    let mut hh: blst::blst_p1 = blst::blst_p1::default();
    let hh_ptr: *const blst::blst_p1 = &hh;
    unsafe {
        blst_hash_to_g1(
            &mut hh,
            input.as_ptr(),
            input.len(),
            dst.as_ptr(),
            dst.len(),
            aug.as_ptr(),
            aug.len(),
        );
    }

    let mut s_bytes: [u8; 32] = [0; 32];
    unsafe {
        let mut s_sca: blst_scalar = blst_scalar::default();
        blst_scalar_from_fr(&mut s_sca, s);
        blst_bendian_from_scalar(s_bytes.as_mut_ptr(), &s_sca);
    }

    let mut uu = blst_p1::default();
    unsafe {
        let mut sgg = blst_p1::default();
        let mut cpk = blst_p1::default();
        blst_p1_mult(
            &mut sgg,
            blst_p1_generator(),
            s_bytes.as_ptr(),
            8 * s_bytes.len(),
        );
        blst_p1_mult(&mut cpk, pk, c.b.as_ptr(), 8 * c.b.len());
        blst_p1_cneg(&mut cpk, true);
        blst_p1_add(&mut uu, &sgg, &cpk);
    }

    let mut vv = blst_p1::default();
    unsafe {
        let gamma_ptr: *const blst::blst_p1 = gamma;
        let mut shh = blst_p1::default();
        let mut cgamma = blst_p1::default();
        blst_p1_mult(&mut shh, hh_ptr, s_bytes.as_ptr(), 8 * s_bytes.len());
        blst_p1_mult(&mut cgamma, gamma_ptr, c.b.as_ptr(), 8 * c.b.len());
        blst_p1_cneg(&mut cgamma, true);
        blst_p1_add(&mut vv, &shh, &cgamma);
    }

    let mut bytes64: [u64; 3 * 3 * 6] = [0; 3 * 3 * 6];
    bytes64[0..6].copy_from_slice(&gamma.x.l);
    bytes64[6..12].copy_from_slice(&gamma.y.l);
    bytes64[12..18].copy_from_slice(&gamma.z.l);
    bytes64[18..24].copy_from_slice(&uu.x.l);
    bytes64[24..30].copy_from_slice(&uu.y.l);
    bytes64[30..36].copy_from_slice(&uu.z.l);
    bytes64[36..42].copy_from_slice(&vv.x.l);
    bytes64[42..48].copy_from_slice(&vv.y.l);
    bytes64[48..54].copy_from_slice(&vv.z.l);
    let bytes8: [u8; 432] = unsafe { std::mem::transmute(bytes64) };
    let mut c1_bytes: [u8; 32] = [0; 32];
    let mut c1 = blst_scalar::default();
    unsafe {
        blst_sha256(c1_bytes.as_mut_ptr(), bytes8.as_ptr(), bytes8.len());
        blst_scalar_from_bendian(&mut c1, c1_bytes.as_ptr());
    }

    c.b == c1.b
}
