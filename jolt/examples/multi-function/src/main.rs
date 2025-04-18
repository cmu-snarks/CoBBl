use std::time::*;
use jolt_sdk::JoltHyperKZGProof as Proof;

const REPEAT: usize = 5;

fn test<T, PF, VF>(b_name: &str, compiler_time: Duration, prove: PF, verify: VF)
    where PF: Fn() -> (T, Proof), VF: Fn(Proof) -> bool
{
    let mut prover_time_avg = 0;
    let mut verifier_time_avg = 0;

    for _ in 0..REPEAT {
        let prover_start = Instant::now();
        let (_, proof) = prove();
        let prover_time = prover_start.elapsed();
        let verifier_start = Instant::now();
        let _ = verify(proof);
        let verifier_time = verifier_start.elapsed();

        prover_time_avg += prover_time.as_millis();
        verifier_time_avg += verifier_time.as_millis();
    }

    prover_time_avg /= REPEAT as u128;
    verifier_time_avg /= REPEAT as u128;

    println!("\n--\n{}", b_name);
    println!("{}ms", compiler_time.as_millis());
    println!("{}ms", prover_time_avg);
    println!("{}ms", verifier_time_avg);    
}

pub fn main() {
    // Find Min
    let b_name = "find_min - max_high 1200";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_find_min_1200();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 0, 1200), verify);

    let b_name = "mat_mult - max_n 5";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_mat_mult_5();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 0, 5), verify);

    let b_name = "mat_mult - max_n 16";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_mat_mult_16();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 0, 16), verify);

    // KMP Search
    let b_name = "kmp_search - max_n 480; max_m 48";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_kmp_search_48();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 480, 48), verify);

    // DNA Align
    let b_name = "dna_align - max_n 5";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_dna_align();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 5), verify);
    let b_name = "dna_align - max_n 30";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_dna_align();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 30), verify);

    // RLE Codec
    let b_name = "rle_codec - max_n 20";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_rle_codec();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 20), verify);
    let b_name = "rle_codec - max_n 60";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_rle_codec();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 0, 60), verify);

    // --
    // SPECIAL
    // --
    // SHA256
    let b_name = "sha256 - max_n 1";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_sha256();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 1), verify);
    let b_name = "sha256 - max_n 6";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_sha256();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(0, 6), verify);

    // Poseidon
    let b_name = "poseidon - max_n 1";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_poseidon();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(1), verify);
    let b_name = "poseidon - max_n 6";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_poseidon();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(6), verify);

    // Compact Cert Simple
    let b_name = "compact_cert - max_n 1";
    let compiler_start = Instant::now();
    let (prove, verify) = guest::build_compact_cert_simple();
    let compiler_time = compiler_start.elapsed();
    test(b_name, compiler_time, || prove(1), verify);
}
