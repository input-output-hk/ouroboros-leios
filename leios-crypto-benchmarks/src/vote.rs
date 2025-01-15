use blst::{min_sig::*, BLST_ERROR};
use rand::RngCore;

pub fn gen_key () -> SecretKey {
  let mut rng: rand::prelude::ThreadRng = rand::thread_rng();
  let mut ikm: [u8; 32] = [0u8; 32];
  rng.fill_bytes(&mut ikm);
  let info = b"";
  SecretKey::key_gen(&ikm, info).unwrap()
}

pub struct VoteSignature {
  pub sigma_eid : Signature,
  pub sigma_m : Signature,
}

const EMPTY : [u8; 0] = [];

const DST : &[u8; 10] = b"Leios vote";

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

pub fn gen_cert(vss : &[&VoteSignature]) -> Result<CertSignature, BLST_ERROR> {
  let sigmas_eid : Vec<&Signature> = vss.iter().map(|vs| &vs.sigma_eid).collect();
  let result_eid = AggregateSignature::aggregate(&sigmas_eid, true);
  let sigmas_m : Vec<&Signature> = vss.iter().map(|vs| &vs.sigma_m).collect();
  let result_m = AggregateSignature::aggregate(&sigmas_m, true);
  match (result_eid, result_m) {
    (Ok(sig_eid), Ok(sig_m) ) => Ok(CertSignature {sigma_tilde_eid : sig_eid.to_signature(), sigma_tilde_m : sig_m.to_signature()}),
    (Err(err), _) => Err(err),
    (_, Err(err)) => Err(err),
  }
}

pub fn verify_cert(pks : &[&PublicKey], eid : &[u8], m : &[u8], cs : &CertSignature) -> bool {
  let result_pk = AggregatePublicKey::aggregate(pks, true);
  match result_pk {
    Ok(pk) => {
      let result_eid = cs.sigma_tilde_eid.verify(true, &EMPTY, DST, eid, &pk.to_public_key(), true);
      let result_m = cs.sigma_tilde_m.verify(true, m, DST, eid, &pk.to_public_key(), true);
      result_eid == BLST_ERROR::BLST_SUCCESS && result_m == BLST_ERROR::BLST_SUCCESS
    },
    Err(_) => false
  }
}