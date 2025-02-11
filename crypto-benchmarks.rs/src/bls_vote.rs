use blst::min_sig::*;
use blst::*;
use rand::RngCore;

use crate::bls_util::*;

const EMPTY: [u8; 0] = [];

const DST: &[u8; 5] = b"Leios";

pub fn gen_key() -> SecretKey {
    let mut rng: rand::prelude::ThreadRng = rand::thread_rng();
    let mut ikm: [u8; 32] = [0u8; 32];
    rng.fill_bytes(&mut ikm);
    let info = b"";
    SecretKey::key_gen(&ikm, info).unwrap()
}

pub fn make_pop(sk: &SecretKey) -> (Signature, Signature) {
    let m1: [u8; 192] = sk.sk_to_pk().serialize();
    let m2 = EMPTY;
    (sk.sign(&m1, DST, b"PoP"), sk.sign(&m2, DST, &EMPTY))
}

pub fn check_pop(pk: &PublicKey, mu1: &Signature, mu2: &Signature) -> bool {
    let m1: [u8; 192] = pk.serialize();
    let m2 = EMPTY;
    let result1 = mu1.verify(true, &m1, DST, b"PoP", pk, true);
    let result2 = mu2.verify(true, &m2, DST, &EMPTY, pk, true);
    result1 == BLST_ERROR::BLST_SUCCESS && result2 == BLST_ERROR::BLST_SUCCESS
}

pub fn gen_sig(sk: &SecretKey, eid: &[u8], m: &[u8]) -> Signature {
    sk.sign(m, DST, eid)
}

pub fn verify_sig(pk: &PublicKey, eid: &[u8], m: &[u8], vs: &Signature) -> bool {
    let result_m = vs.verify(true, m, DST, eid, pk, false);
    result_m == BLST_ERROR::BLST_SUCCESS
}

pub fn gen_sigma_eid(sk: &SecretKey, eid: &[u8]) -> Signature {
    sk.sign(&EMPTY, DST, eid)
}

pub fn gen_vote(sk: &SecretKey, eid: &[u8], m: &[u8]) -> (Signature, Signature) {
    (sk.sign(&EMPTY, DST, eid), sk.sign(m, DST, eid))
}

pub fn verify_vote(pk: &PublicKey, eid: &[u8], m: &[u8], vs: &(Signature, Signature)) -> bool {
    let result_eid = vs.0.verify(true, &EMPTY, DST, eid, pk, true);
    let result_m = vs.1.verify(true, m, DST, eid, pk, false);
    result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
}

fn hash_sigs(sigma_eids: &[&Signature], sigma_ms: &[&Signature]) -> [u8; 32] {
    let mut sigmas: Vec<&Signature> = Vec::new();
    sigmas.extend(sigma_eids);
    sigmas.extend(sigma_ms);
    let msg: Vec<u8> = sigmas.iter().flat_map(|s| s.serialize()).collect();
    unsafe {
        let mut out: [u8; 32] = [0; 32];
        blst_sha256(out.as_mut_ptr(), msg.as_ptr(), msg.len());
        out
    }
}

fn hash_index(i: i32, h: &[u8; 32]) -> [u8; 32] {
    let mut msg: [u8; 36] = [0; 36];
    let ii: [u8; 4] = i.to_ne_bytes();
    msg[0..32].copy_from_slice(h);
    msg[32..36].copy_from_slice(&ii);

    unsafe {
        let mut out: [u8; 32] = [0; 32];
        blst_sha256(out.as_mut_ptr(), msg.as_ptr(), msg.len());
        let mut sca: blst_scalar = blst_scalar::default();
        blst_scalar_from_bendian(&mut sca, out.as_ptr());
        out
    }
}

pub fn gen_cert(vss: &[&(Signature, Signature)]) -> Result<(Signature, Signature), BLST_ERROR> {
    let sigma_eids: Vec<&Signature> = vss.iter().map(|vs| &vs.1).collect();
    let sigma_ms: Vec<&Signature> = vss.iter().map(|vs| &vs.1).collect();
    gen_cert_fa(&sigma_eids, &sigma_ms)
}

pub fn verify_cert(
    pks: &[&PublicKey],
    eid: &[u8],
    m: &[u8],
    vss: &[&(Signature, Signature)],
    cs: &(Signature, Signature),
) -> bool {
    let sigma_eids: Vec<&Signature> = vss.iter().map(|vs| &vs.1).collect();
    let sigma_ms: Vec<&Signature> = vss.iter().map(|vs| &vs.1).collect();
    let h: [u8; 32] = hash_sigs(&sigma_eids, &sigma_ms);

    let f = |i: usize| {
        move |point: blst_p2| {
            let hi: [u8; 32] = hash_index(i as i32, &h);
            let mut point1: blst_p2 = blst_p2::default();
            unsafe {
                blst_p2_mult(&mut point1, &point, hi.as_ptr(), 8 * h.len());
            }
            point1
        }
    };

    let pks1: Vec<PublicKey> = pks
        .iter()
        .enumerate()
        .map(|(i, pk)| pk_transform(&f(i), pk))
        .collect();
    let pk1_refs: Vec<&PublicKey> = pks1.iter().collect();

    let result_pk = AggregatePublicKey::aggregate(pks, true);
    let result_pk1 = AggregatePublicKey::aggregate(&pk1_refs, true);

    match (result_pk, result_pk1) {
        (Ok(pk), Ok(pk1)) => {
            let result_eid =
                cs.0.verify(true, &EMPTY, DST, eid, &pk1.to_public_key(), true);
            let result_m = cs.1.verify(true, m, DST, eid, &pk.to_public_key(), true);
            result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
        }
        _ => false,
    }
}

pub fn gen_cert_fa(
    sigma_eids: &[&Signature],
    sigma_ms: &[&Signature],
) -> Result<(Signature, Signature), BLST_ERROR> {
    let h: [u8; 32] = hash_sigs(sigma_eids, &[]);

    let f = |i: usize| {
        move |point: blst_p1| {
            let hi: [u8; 32] = hash_index(i as i32, &h);
            let mut point1: blst_p1 = blst_p1::default();
            unsafe {
                blst_p1_mult(&mut point1, &point, hi.as_ptr(), 8 * h.len());
            }
            point1
        }
    };
    let sigma_eis_xfmd: Vec<Signature> = sigma_eids
        .iter()
        .enumerate()
        .map(|(i, sigma_eid)| sig_transform(&f(i), sigma_eid))
        .collect();
    let sigma_eid_xfmd_refs: Vec<&Signature> = sigma_eis_xfmd.iter().collect();
    let result_eid = AggregateSignature::aggregate(&sigma_eid_xfmd_refs, true);
    let result_m = AggregateSignature::aggregate(sigma_ms, true);

    match (result_eid, result_m) {
        (Ok(sig_eid), Ok(sig_m)) => Ok((sig_eid.to_signature(), sig_m.to_signature())),
        (Err(err), _) => Err(err),
        (_, Err(err)) => Err(err),
    }
}

pub fn gen_cert_fa_pure(sigma_ms: &[&Signature]) -> Result<Signature, BLST_ERROR> {
    let result_m = AggregateSignature::aggregate(sigma_ms, true);
    match result_m {
        Ok(sig_m) => Ok(sig_m.to_signature()),
        Err(err) => Err(err),
    }
}

pub fn verify_cert_fa(
    pks: &[&PublicKey],
    pks_nonpersistent: &[&PublicKey],
    eid: &[u8],
    m: &[u8],
    sigma_eids: &[&Signature],
    sigma_tilde_eid: &Signature,
    sigma_tilde_m: &Signature,
) -> bool {
    let h: [u8; 32] = hash_sigs(sigma_eids, &[]);

    let f = |i: usize| {
        move |point: blst_p2| {
            let hi: [u8; 32] = hash_index(i as i32, &h);
            let mut point1: blst_p2 = blst_p2::default();
            unsafe {
                blst_p2_mult(&mut point1, &point, hi.as_ptr(), 8 * h.len());
            }
            point1
        }
    };

    let pks1: Vec<PublicKey> = pks_nonpersistent
        .iter()
        .enumerate()
        .map(|(i, pk)| pk_transform(&f(i), pk))
        .collect();
    let pk1_refs: Vec<&PublicKey> = pks1.iter().collect();

    let result_pk = AggregatePublicKey::aggregate(pks, true);
    let result_pk1 = AggregatePublicKey::aggregate(&pk1_refs, true);

    match (result_pk, result_pk1) {
        (Ok(pk), Ok(pk1)) => {
            let result_eid =
                sigma_tilde_eid.verify(true, &EMPTY, DST, eid, &pk1.to_public_key(), true);
            let result_m = sigma_tilde_m.verify(true, m, DST, eid, &pk.to_public_key(), true);
            result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
        }
        _ => false,
    }
}

pub fn verify_cert_fa_pure(
    pks: &[&PublicKey],
    eid: &[u8],
    m: &[u8],
    sigma_tilde_m: &Signature,
) -> bool {
    let result_pk = AggregatePublicKey::aggregate(pks, true);
    match result_pk {
        Ok(pk) => {
            let result_m = sigma_tilde_m.verify(true, m, DST, eid, &pk.to_public_key(), true);
            result_m == BLST_ERROR::BLST_SUCCESS
        }
        _ => false,
    }
}
