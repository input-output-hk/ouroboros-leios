use blst::*;
use blst::min_sig::*;
use rand::RngCore;
use crate::bls::*;
use crate::vrf::sk_to_pk_point;

const EMPTY : [u8; 0] = [];

const DST : &[u8; 5] = b"Leios";

pub fn gen_key() -> SecretKey {
  let mut rng: rand::prelude::ThreadRng = rand::thread_rng();
  let mut ikm: [u8; 32] = [0u8; 32];
  rng.fill_bytes(&mut ikm);
  let info = b"";
  SecretKey::key_gen(&ikm, info).unwrap()
}

pub fn make_pop(sk : &SecretKey) -> (Signature, Signature) {
  let m1 : [u8; 192] = sk.sk_to_pk().serialize();
  let m2 = EMPTY;
  (
    sk.sign(&m1, DST, b"PoP"),
    sk.sign(&m2, DST, &EMPTY),
  )
}

pub fn check_pop(pk : &PublicKey, mu1 : &Signature, mu2 : &Signature) -> bool {
  let m1 : [u8; 192] = pk.serialize();
  let m2 = EMPTY;
  let result1 = mu1.verify(true, &m1, DST, b"PoP", pk, true);
  let result2 = mu2.verify(true, &m2, DST, &EMPTY, pk, true);
  result1 == BLST_ERROR::BLST_SUCCESS && result2 == BLST_ERROR::BLST_SUCCESS
}

pub struct VoteSignature {
  pub sigma_eid : Signature,
  pub sigma_m : Signature,
}

pub fn gen_vote(sk : &SecretKey, eid : &[u8], m : &[u8]) -> VoteSignature {
  VoteSignature {
    sigma_eid : sk.sign(&EMPTY, DST, eid),
    sigma_m : sk.sign(m, DST, eid),
  }
}

pub fn verify_vote(pk : &PublicKey, eid : &[u8], m : &[u8], vs : &VoteSignature) -> bool {
  let result_eid = vs.sigma_eid.verify(true, &EMPTY, DST, eid, &pk, true);
  let result_m = vs.sigma_m.verify(true, m, DST, eid, &pk, false);
  result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
}

pub struct CertSignature {
  pub sigma_tilde_eid : Signature,
  pub sigma_tilde_m : Signature,
}

fn hash_sigs(vss : &[&VoteSignature]) -> [u8; 32] {

  fn serialise_vs(vs : &VoteSignature) -> Vec<u8> {
    [vs.sigma_eid, vs.sigma_m].iter().flat_map(|s| s.serialize()).collect()
  }
  let msg : Vec<u8> = vss.iter().flat_map(|vs| serialise_vs(vs)).collect();

  unsafe {
    let mut out : [u8; 32] = [0; 32];
    blst_sha256(out.as_mut_ptr(), msg.as_ptr(), msg.len());
    out
  }

}

fn hash_index(i : i32, h : &[u8; 32]) -> [u8; 32] {

  let mut msg : [u8; 36] = [0; 36];
  let ii : [u8; 4] = unsafe { std::mem::transmute(i) };
  msg[0..32].copy_from_slice(h);
  msg[32..36].copy_from_slice(&ii);

  unsafe {
    let mut out : [u8; 32] = [0; 32];
    blst_sha256(out.as_mut_ptr(), msg.as_ptr(), msg.len());
    let mut sca : blst_scalar = blst_scalar::default();
    blst_scalar_from_bendian(&mut sca, out.as_ptr());
    out
  }

}

pub fn gen_cert(vss : &[&VoteSignature]) -> Result<CertSignature, BLST_ERROR> {

  let h : [u8; 32] = hash_sigs(vss);
  let f = | i : usize | {
    move | point : blst_p1 | {
      let hi: [u8; 32] = hash_index(i as i32, &h);
      let mut point1 : blst_p1 = blst_p1::default();
      unsafe {
        blst_p1_mult(&mut point1, &point, hi.as_ptr(), 8 * h.len());
      }
      point1
  }};

  let sigmas_eid : Vec<Signature> = vss.iter().enumerate().map(|(i, vs) | sig_transform(&f(i), &vs.sigma_eid)).collect();
  let sigma_eid_refs : Vec<&Signature> = sigmas_eid.iter().map(|sig| sig).collect();
  let result_eid = AggregateSignature::aggregate(&sigma_eid_refs, true);

  let sigmas_m : Vec<&Signature> = vss.iter().map(|vs| &vs.sigma_m).collect();
  let result_m = AggregateSignature::aggregate(&sigmas_m, true);

  match (result_eid, result_m) {
    (Ok(sig_eid), Ok(sig_m) ) => Ok(CertSignature {sigma_tilde_eid : sig_eid.to_signature(), sigma_tilde_m : sig_m.to_signature()}),
    (Err(err), _) => Err(err),
    (_, Err(err)) => Err(err),
  }

}

pub fn verify_cert(pks : &[&PublicKey], eid : &[u8], m : &[u8], vss : &[&VoteSignature], cs : &CertSignature) -> bool {

  let h : [u8; 32] = hash_sigs(vss);
  let f = | i : usize | {
    move | point : blst_p2 | {
      let hi: [u8; 32] = hash_index(i as i32, &h);
      let mut point1 : blst_p2 = blst_p2::default();
      unsafe {
        blst_p2_mult(&mut point1, &point, hi.as_ptr(), 8 * h.len());
      }
      point1
  }};

  let pks1 : Vec<PublicKey> = pks.iter().enumerate().map(|(i, pk)| pk_transform(&f(i), pk)).collect();
  let pk1_refs : Vec<&PublicKey> = pks1.iter().map(|pk| pk).collect();

  let result_pk = AggregatePublicKey::aggregate(pks, true);
  let result_pk1 = AggregatePublicKey::aggregate(&pk1_refs, true);
  match (result_pk, result_pk1) {
    (Ok(pk), Ok(pk1)) => {
      let result_eid = cs.sigma_tilde_eid.verify(true, &EMPTY, DST, eid, &pk1.to_public_key(), true);
      let result_m = cs.sigma_tilde_m.verify(true, m, DST, eid, &pk.to_public_key(), true);
      result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
    },
    _ => false
  }

}