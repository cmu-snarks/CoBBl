mod field;
mod curve;
mod schnorr;
mod poseidon;
mod poseidon_constants;
mod merkle;
mod poseidon_gen;

use crate::field::Fp;
use crate::schnorr::*;
use crate::poseidon::*;
use crate::merkle::*;
use ff::PrimeField;

use std::fs::File;
use std::io::Write;
use rug::{Integer, integer::Order};
use serde::{Serialize};
use std::time::*;

// Attestor info
#[derive(Clone, Serialize)]
struct Attestor {
    sig: Signature,
    pk: PublicKey,
    weight: usize
}
impl Attestor {
    fn new(sig: Signature, pk: PublicKey, weight: usize) -> Attestor {
        Attestor {
            sig,
            pk,
            weight
        }
    }

    fn to_list(&self) -> Vec<Fp> {
        [self.pk.p.x.clone(), self.pk.p.y.clone(), self.pk.q.x.clone(), self.pk.q.y.clone(), Fp::from(self.weight as u64)].to_vec()
    }

    fn hash(&self) -> Fp {
        poseidon(&self.to_list())
    }
}

// Signature Info
#[derive(Clone, Serialize)]
struct Sig {
    l: usize,
    r: usize,
    sig: Option<Signature>
}
impl Sig {
    fn new(l: usize, r: usize, sig: Option<Signature>) -> Sig {
        Sig {
            l,
            r,
            sig
        }
    }

    fn to_list(&self) -> Vec<Fp> {
        if let Some(sig) = &self.sig {
            // Convert sig.s from U512 to Fp
            let s_fp = Fp::from_str_vartime(&format!("{}", sig.s)).unwrap();
            [sig.r.x.clone(), sig.r.y.clone(), s_fp, Fp::from(self.l as u64), Fp::from(self.r as u64)].to_vec()
        } else {
            [Fp::from(0), Fp::from(0), Fp::from(0), Fp::from(self.l as u64), Fp::from(self.r as u64)].to_vec()
        }
    }

    fn hash(&self) -> Fp {
        poseidon(&self.to_list())
    }
}

// Reveal Proof Entry
#[derive(Clone, Serialize)]
struct T {
    i: usize,
    s: Fp,
    pi_s: MerkleProof,
    p: Fp,
    pi_p: MerkleProof,
}
impl T {
    fn new(i: usize, s: Fp, pi_s: MerkleProof, p: Fp, pi_p: MerkleProof) -> T {
        T {
            i,
            s,
            pi_s,
            p,
            pi_p
        }
    }
}

// Proof
#[derive(Clone, Serialize)]
struct CompactCertProof {
    sig_root: Fp,
    signed_weight: usize,
    t_list: Vec<T>
}

// For serialization & compute size
#[derive(Serialize)]
struct CompleteProof {
    compact_cert_proof: CompactCertProof,
    proven_weight: usize,
    k: usize,
    q: usize,
    message: Fp,
    att_len: usize,
    att_root: Fp,
    att_list: Vec<Attestor>,
    sig_list: Vec<Sig>,
}

const NUM_ATTESTORS: usize = 200000;
// const NUM_REVEALS: usize = 1000;

const PROVEN_WEIGHT: usize = 50;
const KNOWLEDGE_SOUNDNESS: usize = 3; // knowledge soundness of 2^{-k}
const MAX_NUM_REVEALS: usize = 200; // num reveals 2^q
const SIG_WIDTH: usize = 253;

// Commit all attestors as a merkle tree
fn trusted_setup(
    attestors: &Vec<Attestor>
) -> MerkleTree {
    build_merkle_tree(&attestors.iter().map(|i| i.to_list()).collect())
}

fn prover(
    attestors: &Vec<Attestor>, 
    proven_weight: usize,
    k: usize, // knowledge error ~2^{-k} 
    q: usize, // <=2^q random oracle queries
    num_reveals: usize,
    message: &Fp, // the message being signed
    att_root: &Fp, // commitment to the attestors (root of merkle tree)
    att_tree: &MerkleTree,
) -> Result<(CompactCertProof, Vec<Attestor>, Vec<Sig>, Vec<usize>), String> {
    let mut signed_weight = 0;
    let mut collected_list = vec![false; attestors.len()];
    
    // Check uniqueness and signature of each attestor
    let mut i = 0;
    for a in attestors {
        // Check signature
        verify_sig(&a.pk, &a.sig, &message);
        signed_weight += a.weight;
        
        collected_list[i] = true;
        i += 1;
    }
    assert!(signed_weight > proven_weight);

    // Convert attestors into sigs structure
    let mut sigs: Vec<Sig> = Vec::new();
    for i in 0..attestors.len() {
        if collected_list[i] {
            sigs.push(Sig::new(
                if i == 0 { 0 } else { sigs[i - 1].r },
                if i == 0 { 0 } else { sigs[i - 1].r } + attestors[i].weight,
                Some(attestors[i].sig.clone())
            ));
        } else {
            sigs.push(Sig::new(
                if i == 0 { 0 } else { sigs[i - 1].r },
                if i == 0 { 0 } else { sigs[i - 1].r },
                None
            ));
        }
    }
    assert!(sigs[sigs.len() - 1].r == signed_weight);

    // Construct merkle tree for sigs
    let sig_tree = build_merkle_tree(&sigs.iter().map(|i| i.to_list()).collect());

    // Map cumulated weight back to index
    // Binary search, lo inclusive, hi exclusive
    // Need to skip signatures with 0 weight (those not selected)
    let int_to_ind = |coin: usize, mut lo: usize, mut hi: usize| -> usize {
        assert!(coin < signed_weight);
        while lo + 1 < hi {
            let mid = (lo + hi - 1) / 2;
            if sigs[mid].l > coin {
                hi = mid;
            } else if sigs[mid].r <= coin {
                lo = mid + 1;
            } else {
                lo = mid;
                hi = mid + 1;
            }
        }
        assert_eq!(lo + 1, hi);
        lo
    };

    // Fiat-Shamir of oracle queries
    // let num_reveals: usize = (k + q).div_ceil((signed_weight / proven_weight).ilog2() as usize);
    println!("Num Reveals: {}", num_reveals);
    let mut t_list = Vec::new();
    let mut att_list = Vec::new();
    let mut sig_list = Vec::new();
    let mut coin_list = Vec::new();
    for j in 0..num_reveals {
        // Produce coin
        let coin_hash_bytes = poseidon(&[Fp::from(j as u64), sig_tree.root.clone(), Fp::from(proven_weight as u64), message.clone(), att_root.clone()]).to_bytes();
        let mut coin: usize = 0;
        for b in coin_hash_bytes {
            coin = (2 * coin + b as usize) % signed_weight;
        }
        let i = int_to_ind(coin, 0, attestors.len());
        coin_list.push(coin);
        att_list.push(attestors[i].clone());
        sig_list.push(sigs[i].clone());

        // Construct Merkle Proof for Sig
        let (sig_leaf_hash, sig_proof) = {
            let leaf_hash = sig_tree.leaf_hashes[i];
            let merkle_proof = prove_merkle(&sig_tree, i);
            (leaf_hash, merkle_proof)
        };

        // Construct Merkle Proof for Att
        let (att_leaf_hash, att_proof) = {
            let leaf_hash = att_tree.leaf_hashes[i];
            let merkle_proof = prove_merkle(att_tree, i);
            (leaf_hash, merkle_proof)
        };

        t_list.push(T::new(i, sig_leaf_hash, sig_proof, att_leaf_hash, att_proof));
    }
    
    Ok((
        CompactCertProof {
            sig_root: sig_tree.root,
            signed_weight,
            t_list
        },
        att_list,
        sig_list,
        coin_list,
    ))
}

fn verifier(
    compact_cert_proof: &CompactCertProof,
    proven_weight: usize,
    k: usize,
    q: usize,
    num_reveals: usize,
    message: &Fp, // the message being signed
    att_len: usize,
    att_root: Fp,
    // List of attestors / sigs provided by the prover
    att_list: &Vec<Attestor>,
    sig_list: &Vec<Sig>,
) {
    let signed_weight = compact_cert_proof.signed_weight;
    assert!(signed_weight > proven_weight);
    // let num_reveals: usize = (k + q).div_ceil((signed_weight / proven_weight).ilog2() as usize);
    assert_eq!(num_reveals, att_list.len());
    assert_eq!(num_reveals, sig_list.len());

    for j in 0..num_reveals {
        // Reproduce coin
        let coin_hash_bytes = poseidon(&[Fp::from(j as u64), compact_cert_proof.sig_root.clone(), Fp::from(proven_weight as u64), message.clone(), att_root]).to_bytes();
        let mut coin: usize = 0;
        for b in coin_hash_bytes {
            coin = (2 * coin + b as usize) % signed_weight;
        }

        let t = &compact_cert_proof.t_list[j];
        // Sig Opening
        verify_merkle(att_len, &t.pi_s, compact_cert_proof.sig_root, t.i, &t.s);
        // Att Opening
        verify_merkle(att_len, &t.pi_p, att_root, t.i, &t.p);
        // Validity of signature
        assert_eq!(att_list[j].hash(), t.p);
        verify_sig(&att_list[j].pk, &sig_list[j].sig.clone().unwrap(), &message);
        // L < coin <= L + Weight
        assert_eq!(sig_list[j].hash(), t.s);
        assert!(sig_list[j].l <= coin && coin < sig_list[j].l + att_list[j].weight);
    }
}

impl std::convert::From<&Fp> for Integer {
    fn from(f: &Fp) -> Self {
        Self::from_digits(f.to_repr().as_ref(), Order::Lsf)
    }
}

fn cobbl() {
    // let percentages: [f32; 8] = [0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95];

    // for percentage in percentages {
    for NUM_REVEALS in [2, 5, 8] {
        // let NUM_REVEALS: usize = (128f32 / (1f32 / percentage).log2()) as usize;

        // println!("PERC: {}, NUM_R: {}", percentage, NUM_REVEALS);

        // Generate message
        let message = Fp::from_str_vartime("6908441180828167112785246881494320159273940089327447106269949444716788494909").unwrap();

        // Generate attestors
        let mut attestors = Vec::new();
        // Record all e's to be used by the circuit
        let mut e_list = Vec::new();
        for i in 0..NUM_ATTESTORS {
            let (pk, sk) = gen();
            let (attestor_sig, e) = sign(&sk, &message);
            attestors.push(Attestor::new(attestor_sig, pk, i));
            e_list.push(e);
        }
        let k = KNOWLEDGE_SOUNDNESS;
        let q = MAX_NUM_REVEALS;

        // TRUSTED SETUP
        let att_tree = trusted_setup(&attestors);
        let att_root = att_tree.root;
        
        // PROVER
        let (compact_cert_proof, att_list, sig_list, coin_list) = prover(&attestors, PROVEN_WEIGHT, k, q, NUM_REVEALS, &message, &att_root, &att_tree).unwrap();

        // VERIFIER
        let verifier_start = Instant::now();
        verifier(&compact_cert_proof, PROVEN_WEIGHT, k, q, NUM_REVEALS, &message, attestors.len(), att_root, &att_list, &sig_list);
        let verifier_time = verifier_start.elapsed();
        println!("\n--\nVerifier time: {}ms", verifier_time.as_millis());

        let complete_proof = CompleteProof {
            compact_cert_proof: compact_cert_proof.clone(), 
            proven_weight: PROVEN_WEIGHT, 
            k, 
            q,
            message, 
            att_len: attestors.len(), 
            att_root, 
            att_list: att_list.clone(), 
            sig_list: sig_list.clone(),
        };
        let proof_size = bincode::serialize(&complete_proof).unwrap().len();
        println!("Proof Size: {}", proof_size);
        println!("Verification Successful!");

        // Generate input for Zok
        let file_name = format!("../benchmarks/compact_cert/{}.input", NUM_REVEALS);
        let mut f = File::create(file_name).unwrap();
        // u32 num_attestors
        writeln!(&mut f, "num_attestors {}", NUM_ATTESTORS).unwrap();
        // For compact_cert_proof
        // field sig_root
        writeln!(&mut f, "sig_root {}", Integer::from(&compact_cert_proof.sig_root)).unwrap();
        // u32 signed_weight,
        writeln!(&mut f, "signed_weight {}", compact_cert_proof.signed_weight).unwrap();
        // u32[0] t_i_list,
        write!(&mut f, "t_i_list [ro ").unwrap();
        for i in &compact_cert_proof.t_list {
            write!(&mut f, "{} ", i.i).unwrap();
        }
        writeln!(&mut f, "]").unwrap();
        // All memory entries within T (just p now)
        // field[0] t_mem,
        write!(&mut f, "t_mem [ro ").unwrap();
        let merkle_depth: usize = NUM_ATTESTORS.next_power_of_two().ilog2().div_ceil(1).try_into().unwrap();
        // p
        for p in &att_list {
            for e in &p.to_list() {
                write!(&mut f, "{} ", Integer::from(e)).unwrap();
            }
        }
        writeln!(&mut f, "]").unwrap();
        // List of pointers (input format field[0])
        let num_reveals = att_list.len();
        // field[0][0] t_p_list,
        write!(&mut f, "t_p_list [ro ").unwrap();
        for p in (0..num_reveals).map(|i| num_reveals + i * 5) {
            write!(&mut f, "{} ", p).unwrap();
        }
        writeln!(&mut f, "]").unwrap();
        // For others
        // u32 proven_weight,
        writeln!(&mut f, "proven_weight {}", PROVEN_WEIGHT).unwrap();
        // u32 num_reveals,
        writeln!(&mut f, "num_reveals {}", num_reveals).unwrap();
        // field message,
        writeln!(&mut f, "message {}", Integer::from(&message)).unwrap();
        // u32 merkle_depth,
        writeln!(&mut f, "merkle_depth {}", merkle_depth).unwrap();
        // field att_root,
        writeln!(&mut f, "att_root {}", Integer::from(&att_root)).unwrap();
        // field[0] coins
        write!(&mut f, "coins [ro ").unwrap();
        for c in coin_list {
            write!(&mut f, "{} ", c).unwrap();
        }
        writeln!(&mut f, "]").unwrap();
        write!(&mut f, "END").unwrap();

        // Supply i_bits, e_bits, and s_bits as witnesses
        let file_name = format!("../benchmarks/compact_cert/{}.witness", NUM_REVEALS);
        let mut f = File::create(file_name).unwrap();
        // field[0] e_s_mem,
        for i in 0..num_reveals {
            // s: sig_r_x, sig_r_y, sig_s, l, r
            for e in &sig_list[i].to_list() {
                write!(&mut f, "{} ", Integer::from(e)).unwrap();
            }
            // i_bits
            let next_att = compact_cert_proof.t_list[i].i;
            let mut next_i = compact_cert_proof.t_list[i].i.clone();
            // Split i.i into LITTLE ENDIAN bits, with len = log(NUM_ATTESTORS) rounded up
            let mut i_bits = Vec::new();
            for _ in 0..merkle_depth {
                i_bits.push(next_i % 2);
                next_i /= 2;
            }
            for j in 0..merkle_depth {
                // i_bits
                write!(&mut f, "{} ", i_bits[j]).unwrap();
                // pi_s.path
                write!(&mut f, "{} ", Integer::from(&compact_cert_proof.t_list[i].pi_s.path[j])).unwrap();
                // pi_p.path
                write!(&mut f, "{} ", Integer::from(&compact_cert_proof.t_list[i].pi_p.path[j])).unwrap();
            }
            // e_bits, s_bits
            let mut e = e_list[next_att].clone();
            let mut s = Integer::from(&sig_list[i].to_list()[2]).clone();
            // Split e and s into SIG_WIDTH big endian bits
            let mut e_bits = Vec::new();
            let mut s_bits = Vec::new();
            for _ in 0..SIG_WIDTH {
                e_bits.insert(0, e.clone() % 2);
                e /= 2;
                s_bits.insert(0, s.clone() % 2);
                s /= 2;
            }
            for j in 0..SIG_WIDTH - 1 {
                write!(&mut f, "{} {} ", e_bits[j], s_bits[j]).unwrap();
            }
            writeln!(&mut f, "{} {}", e_bits[SIG_WIDTH - 1], s_bits[SIG_WIDTH - 1]).unwrap();
        }
        write!(&mut f, "END").unwrap();
    }

    // Generate poseidon file
    // poseidon_gen::poseidon_gen(2, 2);
    // poseidon_gen::poseidon_gen(3, 1);
    // poseidon_gen::poseidon_gen(5, 2);
}

fn circ() {
    // let percentages: [f32; 8] = [0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95];

    for NUM_REVEALS in [2, 5, 8] {
        // let NUM_REVEALS: usize = (128f32 / (1f32 / percentage).log2()) as usize;

        // println!("PERC: {}, NUM_R: {}", percentage, NUM_REVEALS);

        // Generate message
        let message = Fp::from_str_vartime("6908441180828167112785246881494320159273940089327447106269949444716788494909").unwrap();

        // Generate attestors
        let mut attestors = Vec::new();
        // Record all e's to be used by the circuit
        let mut e_list = Vec::new();
        for i in 0..NUM_ATTESTORS {
            let (pk, sk) = gen();
            let (attestor_sig, e) = sign(&sk, &message);
            attestors.push(Attestor::new(attestor_sig, pk, i));
            e_list.push(e);
        }
        let k = KNOWLEDGE_SOUNDNESS;
        let q = MAX_NUM_REVEALS;

        // TRUSTED SETUP
        let att_tree = trusted_setup(&attestors);
        let att_root = att_tree.root;
        
        // PROVER
        let (compact_cert_proof, att_list, sig_list, coin_list) = prover(&attestors, PROVEN_WEIGHT, k, q, NUM_REVEALS, &message, &att_root, &att_tree).unwrap();

        // VERIFIER
        let verifier_start = Instant::now();
        verifier(&compact_cert_proof, PROVEN_WEIGHT, k, q, NUM_REVEALS, &message, attestors.len(), att_root, &att_list, &sig_list);
        let verifier_time = verifier_start.elapsed();
        println!("\n--\nVerifier time: {}ms", verifier_time.as_millis());

        let complete_proof = CompleteProof {
            compact_cert_proof: compact_cert_proof.clone(), 
            proven_weight: PROVEN_WEIGHT, 
            k, 
            q,
            message, 
            att_len: attestors.len(), 
            att_root, 
            att_list: att_list.clone(), 
            sig_list: sig_list.clone(),
        };
        let proof_size = bincode::serialize(&complete_proof).unwrap().len();
        println!("Proof Size: {}", proof_size);
        println!("Verification Successful!");

        // Generate Zok main function
        let file_name = format!("../benchmarks/compact_cert_circ/main_{}.zok", NUM_REVEALS);
        let mut f = File::create(file_name).unwrap();
        writeln!(&mut f, "from \"./poseidon_struct.zok\" import DoubleHash").unwrap();
        writeln!(&mut f, "from \"./poseidon2.zok\" import poseidon2_batch2").unwrap();
        writeln!(&mut f, "from \"./poseidon3.zok\" import poseidon3").unwrap();
        writeln!(&mut f, "from \"./poseidon5.zok\" import poseidon5_batch2").unwrap();
        writeln!(&mut f, "from \"./merkle.zok\" import MerkleProof, verify_merkle, verify_merkle_batch").unwrap();
        writeln!(&mut f, "from \"./schnorr.zok\" import Point, DoublePoint, QuadPoint, PublicKey, Signature, verify_signature, point_add, point_mul, point_double_add_batch, point_mul_batch").unwrap();
        writeln!(&mut f, "from \"./compact_cert.zok\" import NUM_REVEALS_F, T, CompactCertProof, verifier").unwrap();
        writeln!(&mut f, "").unwrap();
        writeln!(&mut f, "def main(").unwrap();
        writeln!(&mut f, "    field num_attestors,").unwrap();
        writeln!(&mut f, "    // For compact_cert_proof").unwrap();
        writeln!(&mut f, "    field sig_root,").unwrap();
        writeln!(&mut f, "    field signed_weight,").unwrap();
        writeln!(&mut f, "    // For others").unwrap();
        writeln!(&mut f, "    field proven_weight,").unwrap();
        writeln!(&mut f, "    field num_reveals,").unwrap();
        writeln!(&mut f, "    field message,").unwrap();
        writeln!(&mut f, "    // field merkle_depth,").unwrap();
        writeln!(&mut f, "    field att_root,").unwrap();
        let num_reveals = att_list.len();
        let merkle_depth: usize = NUM_ATTESTORS.next_power_of_two().ilog2().div_ceil(1).try_into().unwrap();
        for i in 0..num_reveals {
            writeln!(&mut f, "    field i_{},", i).unwrap();
            for j in 0..merkle_depth {
                writeln!(&mut f, "    field i_bits_{}_{},", i, j).unwrap();
            }
            let s_i_list = sig_list[i].to_list();
            for j in 0..s_i_list.len() {
                writeln!(&mut f, "    field s_{}_{},", i, j).unwrap();
            }
            for j in 0..merkle_depth {
                writeln!(&mut f, "    field pi_s_{}_{},", i, j).unwrap();
            }
            let p_i_list = att_list[i].to_list();
            for j in 0..p_i_list.len() {
                writeln!(&mut f, "    field p_{}_{},", i, j).unwrap();
            }
            for j in 0..merkle_depth {
                writeln!(&mut f, "    field pi_p_{}_{},", i, j).unwrap();
            }

            for j in 0..SIG_WIDTH {
                writeln!(&mut f, "    field e_bits_list_{}_{},", i, j).unwrap();
            }
            for j in 0..SIG_WIDTH {
                writeln!(&mut f, "    field s_bits_list_{}_{},", i, j).unwrap();
            }
            if i == num_reveals - 1 {
                writeln!(&mut f, "    field coins_{}", i).unwrap();
            } else {
                writeln!(&mut f, "    field coins_{},", i).unwrap();
            }
        }
        writeln!(&mut f, ") -> field:").unwrap();
        writeln!(&mut f, "    CompactCertProof compact_cert_proof = CompactCertProof {{").unwrap();
        writeln!(&mut f, "        sig_root: sig_root,").unwrap();
        writeln!(&mut f, "        signed_weight: signed_weight,").unwrap();
        writeln!(&mut f, "        t_list: [").unwrap();
        for i in 0..num_reveals {
            writeln!(&mut f, "            T {{").unwrap();
            writeln!(&mut f, "                i: i_{},", i).unwrap();
            // i_bits
            write!(&mut f, "                i_bits: [").unwrap();
            for j in 0..merkle_depth - 1 {
                write!(&mut f, "i_bits_{}_{}, ", i, j).unwrap();
            }
            writeln!(&mut f, "i_bits_{}_{}],", i, merkle_depth - 1).unwrap();
            // s
            let s_i_list = sig_list[i].to_list();
            write!(&mut f, "                s: [").unwrap();
            for j in 0..s_i_list.len() - 1 {
                write!(&mut f, "s_{}_{}, ", i, j).unwrap();
            }
            writeln!(&mut f, "s_{}_{}],", i, s_i_list.len() - 1).unwrap();
            // pi_s
            write!(&mut f, "                pi_s: MerkleProof {{ path: [").unwrap();
            for j in 0..merkle_depth - 1 {
                write!(&mut f, "pi_s_{}_{}, ", i, j).unwrap();
            }
            writeln!(&mut f, "pi_s_{}_{}]}},", i, merkle_depth - 1).unwrap();
            // p
            let p_i_list = att_list[i].to_list();
            write!(&mut f, "                p: [").unwrap();
            for j in 0..p_i_list.len() - 1 {
                write!(&mut f, "p_{}_{}, ", i, j).unwrap();
            }
            writeln!(&mut f, "p_{}_{}],", i, p_i_list.len() - 1).unwrap();
            // pi_p
            write!(&mut f, "                pi_p: MerkleProof {{ path: [").unwrap();
            for j in 0..merkle_depth - 1 {
                write!(&mut f, "pi_p_{}_{}, ", i, j).unwrap();
            }
            writeln!(&mut f, "pi_p_{}_{}]}},", i, merkle_depth - 1).unwrap();
            // END
            if i == num_reveals - 1 {
                writeln!(&mut f, "            }}").unwrap();
            } else {
                writeln!(&mut f, "            }},").unwrap();
            }
        }
        writeln!(&mut f, "        ]").unwrap();
        writeln!(&mut f, "    }}").unwrap();

        // e_bits_list
        writeln!(&mut f, "    field[{}][{}] e_bits_list = [", num_reveals, SIG_WIDTH).unwrap();
        for i in 0..num_reveals {
            write!(&mut f, "        [").unwrap();
            for j in 0..SIG_WIDTH - 1 {
                write!(&mut f, "e_bits_list_{}_{}, ", i, j).unwrap();
            }
            if i == num_reveals - 1 {
                writeln!(&mut f, "e_bits_list_{}_{}]", i, SIG_WIDTH - 1).unwrap();
            } else {
                writeln!(&mut f, "e_bits_list_{}_{}],", i, SIG_WIDTH - 1).unwrap();
            }
        }
        writeln!(&mut f, "    ]").unwrap();
        // s_bits_list
        writeln!(&mut f, "    field[{}][{}] s_bits_list = [", num_reveals, SIG_WIDTH).unwrap();
        for i in 0..num_reveals {
            write!(&mut f, "        [").unwrap();
            for j in 0..SIG_WIDTH - 1 {
                write!(&mut f, "s_bits_list_{}_{}, ", i, j).unwrap();
            }
            if i == num_reveals - 1 {
                writeln!(&mut f, "s_bits_list_{}_{}]", i, SIG_WIDTH - 1).unwrap();
            } else {
                writeln!(&mut f, "s_bits_list_{}_{}],", i, SIG_WIDTH - 1).unwrap();
            }
        }
        writeln!(&mut f, "    ]").unwrap();
        // coin
        write!(&mut f, "    field[{}] coins = [", num_reveals).unwrap();
        for i in 0..num_reveals - 1 {
            write!(&mut f, "coins_{}, ", i).unwrap();
        }
        writeln!(&mut f, "coins_{}]", num_reveals - 1).unwrap();
        // FUNC CALL
        writeln!(&mut f, "    return verifier(").unwrap();
        writeln!(&mut f, "        compact_cert_proof,").unwrap();
        writeln!(&mut f, "        proven_weight,").unwrap();
        writeln!(&mut f, "        // num_reveals,").unwrap();
        writeln!(&mut f, "        message,").unwrap();
        writeln!(&mut f, "        // merkle_depth,").unwrap();
        writeln!(&mut f, "        att_root,").unwrap();
        writeln!(&mut f, "        e_bits_list,").unwrap();
        writeln!(&mut f, "        s_bits_list,").unwrap();
        writeln!(&mut f, "        coins").unwrap();
        writeln!(&mut f, "    )").unwrap();

        // Generate input for Zok
        let file_name = format!("../benchmarks/compact_cert_circ/main_{}.input", NUM_REVEALS);
        let mut f = File::create(file_name).unwrap();
        // u32 num_attestors
        writeln!(&mut f, "num_attestors {}", NUM_ATTESTORS).unwrap();
        // For compact_cert_proof
        // field sig_root
        writeln!(&mut f, "sig_root {}", Integer::from(&compact_cert_proof.sig_root)).unwrap();
        // u32 signed_weight,
        writeln!(&mut f, "signed_weight {}", compact_cert_proof.signed_weight).unwrap();
        // For others
        // u32 proven_weight,
        writeln!(&mut f, "proven_weight {}", PROVEN_WEIGHT).unwrap();
        // u32 num_reveals,
        writeln!(&mut f, "num_reveals {}", num_reveals).unwrap();
        // field message,
        writeln!(&mut f, "message {}", Integer::from(&message)).unwrap();
        // field att_root,
        writeln!(&mut f, "att_root {}", Integer::from(&att_root)).unwrap();

        for i in 0..num_reveals {
            // i
            writeln!(&mut f, "i_{} {}", i, compact_cert_proof.t_list[i].i).unwrap();
            // i_bits
            let next_att = compact_cert_proof.t_list[i].i;
            let mut next_i = compact_cert_proof.t_list[i].i.clone();
            // Split i.i into LITTLE ENDIAN bits, with len = log(NUM_ATTESTORS) rounded up
            let mut i_bits = Vec::new();
            for _ in 0..merkle_depth {
                i_bits.push(next_i % 2);
                next_i /= 2;
            }
            // i_bits
            for j in 0..merkle_depth {
                writeln!(&mut f, "i_bits_{}_{} {} ", i, j, i_bits[j]).unwrap();
            }
            // s
            let s_i_list = sig_list[i].to_list();
            for j in 0..s_i_list.len() {
                writeln!(&mut f, "s_{}_{} {}", i, j, Integer::from(&s_i_list[j])).unwrap();
            }
            // pi_s
            for j in 0..merkle_depth {
                writeln!(&mut f, "pi_s_{}_{} {}", i, j, Integer::from(&compact_cert_proof.t_list[i].pi_s.path[j])).unwrap();
            }
            // p
            let p_i_list = att_list[i].to_list();
            for j in 0..p_i_list.len() {
                writeln!(&mut f, "p_{}_{} {}", i, j, Integer::from(&p_i_list[j])).unwrap();
            }
            // pi_p
            for j in 0..merkle_depth {
                writeln!(&mut f, "pi_p_{}_{} {}", i, j, Integer::from(&compact_cert_proof.t_list[i].pi_p.path[j])).unwrap();
            }

            // e_bits_list, s_bits
            let mut e = e_list[next_att].clone();
            let mut s = Integer::from(&sig_list[i].to_list()[2]).clone();
            // Split e and s into SIG_WIDTH big endian bits
            let mut e_bits = Vec::new();
            let mut s_bits = Vec::new();
            for _ in 0..SIG_WIDTH {
                e_bits.insert(0, e.clone() % 2);
                e /= 2;
                s_bits.insert(0, s.clone() % 2);
                s /= 2;
            }
            for j in 0..SIG_WIDTH {
                writeln!(&mut f, "e_bits_list_{}_{} {}", i, j, e_bits[j]).unwrap();
            }
            for j in 0..SIG_WIDTH {
                writeln!(&mut f, "s_bits_list_{}_{} {}", i, j, s_bits[j]).unwrap();
            }
            // field[0] coins
            writeln!(&mut f, "coins_{} {}", i, coin_list[i]).unwrap();
        }
        write!(&mut f, "END").unwrap();
    }

    // Generate poseidon file
    // poseidon_gen::poseidon_gen(2, 2);
    // poseidon_gen::poseidon_gen(3, 1);
    // poseidon_gen::poseidon_gen(5, 2);
}

fn main() {
    cobbl();
    // circ();
}