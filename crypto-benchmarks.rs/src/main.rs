use blst::min_sig::PublicKey;
use blst::min_sig::SecretKey;
use blst::min_sig::Signature;
use leios_crypto_benchmarks::bls::*;
use leios_crypto_benchmarks::sortition::*;
use leios_crypto_benchmarks::vote::*;
use leios_crypto_benchmarks::vrf::*;
use rustc_apfloat::ieee::Quad;

fn main() {
    let f: Quad = "4.8771764574959465286614323309274434524463393558834E-2"
        .parse::<Quad>()
        .unwrap();
    let f1: Quad = ln_1_minus(f);
    let s: Quad = into_quad(0.001);
    let p: f64 = 1.0 - (1.0 - 4.8771764574959465e-2_f64).powf(0.001_f64);
    let p0: Quad = into_quad(p - 1e-15);
    let p1: Quad = into_quad(p + 1e-15);
    println!(
        "ln(1 - f) = {} vs {}",
        (1.0 - 4.8771764574959465e-2_f64).ln(),
        f1
    );
    println!("1 - (1 -f)^s = {} vs {} ", p, leader_value(f1, s));
    println!("Lower: {}", leader_check(f1, s, p0));
    println!("Upper: {}", leader_check(f1, s, p1));

    let votes: Quad = into_quad(500.0);
    let mut pv: Quad = into_quad(0.0);
    loop {
        pv = (pv + into_quad(0.01)).value;
        if pv > into_quad(1.0) {
            break;
        }
        println!("{} {}", pv, voter_check(votes, s, pv))
    }

    let sk = sk_random();
    let pk = sk_to_pk_point(&sk);
    let input = b"The VRF input.";
    let dst = b"Praos RB";
    let (gamma, c, s) = vrf_prove(&sk, input, dst);
    println!("{:?}", gamma);
    println!("{:?}", c);
    println!("{:?}", s);
    println!("{}", vrf_verify(&pk, input, dst, &gamma, &c, &s));

    {
        let sks: Vec<SecretKey> = (0..3).map(|_| gen_key()).collect();
        println!("sks.len() = {}", sks.len());
        let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.sk_to_pk()).collect();
        println!("{:?}", sks[0]);
        println!("{:?}", pks[0]);
        println!("{:?}", pks[0].serialize());
        let xf = |point| {
            println!("{:?}", point);
            point
        };
        pk_transform(&xf, &pks[0]);
        let pk_refs: Vec<&PublicKey> = pks.iter().collect();
        let eid = b"Election ID";
        let m: [u8; 500] = [0; 500];
        let vss: Vec<(Signature, Signature)> = sks.iter().map(|sk| gen_vote(sk, eid, &m)).collect();
        let vs_refs: Vec<&(Signature, Signature)> = vss.iter().collect();
        let cs: (Signature, Signature) = gen_cert(&vs_refs).unwrap();
        println!("{:?}", cs.0);
        println!("{}", verify_cert(&pk_refs, eid, &m, &vs_refs, &cs));

        let (mu1, mu2) = make_pop(&sks[0]);
        println!("pop = {}", check_pop(&pks[0], &mu1, &mu2));
    }
}
