#![cfg_attr(feature = "guest", no_std)]
#![no_main]

use ff::{Field, PrimeField};
use rs_sha256::{HasherContext, Sha256Hasher};
use serde::{Serialize, Deserialize};
use alloc::vec;

// Find Min
#[jolt::provable(stack_size = 10000, memory_size = 10000000)]
fn find_min_1200(low: u32, b: u32, c: u32, high: u32) -> u32 {
    let mut arr: Vec<u32> = vec![0; high as usize];
    let mut sum: u32 = 0;
    for i in 0..high {
        sum = sum + i;
        arr[i as usize] = sum;
    }
    // random access to ensure array is written in memory
    let x = arr[b as usize];

    let mut min = arr[low as usize];
    let mut min_idx = low;

    let mut i = low + 1;
    while i < high {
        if arr[i as usize] < min {
            min = arr[i as usize];
            min_idx = i;
        }
        i = i + 1;
    }

    return min + (min_idx + x) * c;
}


// Mat Mult
fn get_index(i: u32, j: u32, n: u32) -> u32 {
    return n * i + j;
}
#[jolt::provable]
fn mat_mult_5(x: u32, y: u32, z: u32, n: u32) -> u32 {
    let mut a: Vec<u32> = vec![0; 25];
    let mut b: Vec<u32> = vec![0; 25];
    let mut c: Vec<u32> = vec![0; (5 * n) as usize];

    for i in 0..25 {
        a[i as usize] = i;
        b[i as usize] = 2 * i;
    }
    // random access to ensure array is written in memory
    let c1 = a[x as usize];
    let c2 = b[y as usize];

    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            let mut k = 0;
            while k < n {
                c[get_index(i, k, n) as usize] += a[get_index(i, j, 5) as usize] * b[get_index(j, k, n) as usize];
                k = k + 1;
            }
            j = j + 1
        }
        i = i + 1;
    }


    let c3 = c[z as usize];

    return c1 * c2 * c3
}
#[jolt::provable]
fn mat_mult_16(x: u32, y: u32, z: u32, n: u32) -> u32 {
    let mut a: Vec<u32> = vec![0; 256];
    let mut b: Vec<u32> = vec![0; 256];
    let mut c: Vec<u32> = vec![0; 16 * n as usize];

    for i in 0..256 {
        a[i as usize] = i;
        b[i as usize] = 2 * i;
    }
    // random access to ensure array is written in memory
    let c1 = a[x as usize];
    let c2 = b[y as usize];

    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            let mut k = 0;
            while k < n {
                c[get_index(i, k, n) as usize] += a[get_index(i, j, 16) as usize] * b[get_index(j, k, n) as usize];
                k = k + 1;
            }
            j = j + 1
        }
        i = i + 1;
    }


    let c3 = c[z as usize];

    return c1 * c2 * c3
}

// Kmp Search
#[jolt::provable(stack_size = 10000, memory_size = 10000000)]
fn kmp_search_48(b: u32, c: u32, n: u32, m: u32) -> u32 {
    let mut txt: Vec<u32> = vec![0; n as usize];
    let mut pat: Vec<u32> = vec![0; m as usize];

    // Initialize arrays
    let mut sum = 0;
    for i in 0..n {
        sum = sum + i;
        txt[i as usize] = sum;
    }
    for i in 0..48 {
        pat[i as usize] = txt[(n - m - b + i) as usize];
    }
    // random access to ensure array is written in memory
    let x = pat[b as usize];
    let y = txt[b as usize];

    // Generate LPS
    let lps = lps_gen_48(m, &pat);

    let mut i = 0;
    let mut j = 0;
    let mut found = 0;

    while m - j <= n - i {
        if pat[j as usize] == txt[i as usize] {
            i = i + 1;
            j = j + 1;
        }

        if j == m {
            j = lps[(j - 1)  as usize];
            found = i - j;
        } else {
            if i < n && pat[j as usize] != txt[i as usize] {
                if j != 0 {
                    j = lps[(j - 1)  as usize];
                } else {
                    i = i + 1;
                }
            }
        }
    }

    return found + (x + y) * c;
}
fn lps_gen_48(m: u32, pat: &Vec<u32>) -> Vec<u32> {
    let mut lps: Vec<u32> = vec![0; m as usize];
    let mut len = 0;
    let mut i = 1;

    while i < m {
        if pat[i as usize] == pat[len as usize] {
            len = len + 1;
            lps[i as usize] = len;
            i = i + 1;
        } else {
            if len != 0 {
                len = lps[(len - 1) as usize];
            } else {
                i = i + 1;
            }
        }
    }

    return lps;
}

// Dna Align
/*
 * Computes the Longest Common Subsequence of two strings, one of 
 * length m and the other of length n in O(m*n) time
 */
#[jolt::provable]
fn dna_align(x: u32, n: u32) -> u32 {
    let mut a: Vec<u32> = vec![0; n as usize];
    let mut b: Vec<u32> = vec![0; n as usize];

    let mut sum: u32 = 0;
    for i in 0..n {
        sum = sum + i;
        a[i as usize] = sum;
        b[i as usize] = 10 - sum;
    }

    let mut lcs: Vec<u32> = vec![0; n as usize];
    let arr_size: u32 = n;

    // Dynamic programming memo
    let mut ll: Vec<u32> = vec![0; (n * n + n + 1) as usize];
    // Hold choices made at each step, for use when backtracking
    let mut choices: Vec<u32> = vec![0; (n * n + n + 1) as usize];
    // Used when backtracking
    let mut diag: u32;
    let mut down: u32;
    let mut right: u32;

    // Go backwards from i = n-1 downto 0
    let mut i: u32 = n - 1;
    while i + 1 > 0 {
        let mut j: u32 = n - 1;
        while j + 1 > 0 {
            if a[i as usize] == b[j as usize] {
                if i+1 < n && j+1 < n {
                    diag = ll[((i+1) * arr_size + j+1) as usize];
                } else {
                    diag = 0;
                }
                // Diagonal jump
                ll[(i * arr_size + j) as usize] = 1 + diag;
                choices[(i * arr_size + j) as usize] = 0;
            } else {
                if i+1 < n && j < n {
                    down = ll[((i+1) * arr_size + j) as usize];
                } else { 
                    down = 0;
                }
                if i < n && j+1 < n {
                    right = ll[(i * arr_size + j+1) as usize];
                } else {
                    right = 0;
                }
                // Assertion: down and right differ by at most 1
                if down == right + 1 {
                    // Jump down
                    ll[(i * arr_size + j) as usize] = down;
                    choices[(i * arr_size + j) as usize] = 1;
                } else {
                    // Jump right if down == right or right == down + 1.
                    ll[(i * arr_size + j) as usize] = right;
                    choices[(i * arr_size + j) as usize] = 2;
                }
            }
            j = j - 1;
        }
        i = i - 1;
    }


    // Construct LCS, allowing it to have intermittent zero characters
    let mut i_ptr: u32 = 0;
    let mut j_ptr: u32 = 0; // Pointers to where in LL we are with respect to backtracking

    let mut i = 0;
    while i < n {
        lcs[i as usize] = 0; //If A[i] is not in the LCS, this remains 0.
        let mut j = 0;
        while j < n {
            if i == i_ptr && j == j_ptr { // Loop until we meet up with the i_ptr and j_ptr
                if choices[(i * arr_size + j) as usize] == 0 { // we made a diagonal jump here
                    lcs[i as usize] = a[i as usize];
                    i_ptr = i_ptr + 1;
                    j_ptr = j_ptr + 1;
                } else {
                    if choices[(i * arr_size + j) as usize] == 1 { // jump down
                        i_ptr = i_ptr + 1;
                    } else { // jump right
                        j_ptr = j_ptr + 1;
                    }
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }

    // Now move any string terminator (\0) characters in LCS to the end ala insertion sort
    let mut i = 1;
    while i < n {
        let mut inserted = 0;
        let mut j = 0;
        while j < i {
            if lcs[j as usize] == 0 && inserted == 0 {
                // Swap LCS[j] and LCS[i].
                lcs[j as usize] = lcs[i as usize];
                lcs[i as usize] = 0;
                inserted = 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    return lcs[x as usize];
}

// RLE Codec
#[jolt::provable]
fn rle_codec(x: u32, y: u32, n: u32) -> u32 {
    let mut txt: Vec<u32> = vec![0; n as usize];

    // Initialize array
    let mut next_gap: u32 = 1;
    let mut gap: u32 = next_gap;
    for i in 0..20 {
        txt[i as usize] = next_gap;
        gap = gap - 1;
        if gap == 0 {
            next_gap = next_gap + 1;
            gap = next_gap;
        }
    }

    // compress
    let mut compr: Vec<u32> = vec![0; (2 * n) as usize];
    let m = compress(n, &txt, &mut compr);

    // decompress
    let mut out: Vec<u32> = vec![0; n as usize];
    let p = decompress(m, &compr, &mut out);

    assert!(n == p);
    let mut i:u32 = 0;
    while i < n {
        assert!(txt[i as usize] == out[i as usize]);
        i = i + 1;
    }

    return (txt[x as usize] + compr[x as usize] + out[x as usize]) * y;
}
fn compress(n: u32, txt: &Vec<u32>, compr: &mut Vec<u32>) -> u32 {
    // worst case is no compression, in which case we actually double
    // the size of the string!  Note that we could avoid this with a
    // different encoding strategy, but for our purposes the *performance*
    // of the two strategies is little different, and no one is sweating
    // our Weissman Score here. ;)
    let mut next_c: u32 = 0;
    let mut next_t: u32 = 0;
    let mut next_data = txt[0];
    let mut next_count: u32 = 0;

    while next_t < n {
        if txt[next_t as usize] == next_data {
            next_count = next_count + 1;
        } else {
            compr[next_c as usize] = next_data;
            compr[(next_c + 1)  as usize] = next_count;
            next_c = next_c + 2;
            next_data = txt[next_t as usize];
            next_count = 1;
        }
        next_t = next_t + 1;
    }

    // write out the last one
    compr[next_c as usize] = next_data;
    compr[(next_c + 1) as usize] = next_count;
    next_c = next_c + 2;
    
    return next_c;
}
fn decompress(m: u32, compr: &Vec<u32>, out: &mut Vec<u32>) -> u32 {
    let mut next_c: u32 = 0;
    let mut next_t: u32 = 0;

    while next_c < m {
        let next_data = compr[next_c as usize];
        let mut next_count = compr[(next_c + 1) as usize];
        while next_count > 0 {
            out[next_t as usize] = next_data;
            next_t = next_t + 1;
            next_count = next_count - 1;
        }
        next_c = next_c + 2;
    }
    
    return next_t;
}

// SHA 256
#[jolt::provable(stack_size = 10000, memory_size = 10000000)]
fn sha256(m: u32, n: u32) -> u8 {
    let mut hash = 0;

    let mut i = 0;
    while i < n {
        let mut sha256hasher = Sha256Hasher::default();
        let mut padded_message: [u8; 64] = [0; 64];
        let mut sum: u8 = 0;
        for i in 0..16 {
            sum = sum + i;
            padded_message[i as usize] = sum;
        }
        let bytes_result = HasherContext::finish(&mut sha256hasher);
        hash = hash + bytes_result[m as usize];
        i = i + 1;
    }
    return hash;
}

// Poseidon
#[derive(PrimeField, Serialize, Deserialize)]
#[PrimeFieldModulus = "7237005577332262213973186563042994240857116359379907606001950938285454250989"]
#[PrimeFieldGenerator = "9"]
#[PrimeFieldReprEndianness = "little"]
pub struct Fp([u64; 4]);
impl Fp {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.map(|i| i.to_ne_bytes()).concat().try_into().unwrap()
    }
}

fn ark(n: u32, mut state: [Fp; 7], c: [Fp; 455], it: u32) -> [Fp; 7] {
    let mut i: u32 = 0;
    while i < n {
        state[i as usize] = state[i as usize] + c[(it + i) as usize];
        i = i + 1;
    }
    return state
}

fn sbox(n: u32, mut state: [Fp; 7], f: u32, p: u32, r: u32) -> [Fp; 7] {
    state[0] = state[0] * state[0] * state[0] * state[0] * state[0];
    let mut i = 1;
    while i < n {
        state[i as usize] = if (r < f/2) || (r >= f/2 + p) { state[i as usize] * state[i as usize] * state[i as usize] * state[i as usize] * state[i as usize] } else { state[i as usize] };
        i = i + 1;
    }
    return state;
}

fn mix(n: u32, state: [Fp; 7], m: [Fp; 49]) -> [Fp; 7] {
    let mut out: [Fp; 7] = [Fp::from(0); 7];
    let mut i = 0;
    while i < n {
        let mut acc: Fp = Fp::from(0);
        let mut j = 0;
        while j < n {
            acc = acc + (state[j as usize] * m[(i * 2 + j) as usize]);
            j = j + 1;
        }
        out[i as usize] = acc;
        i = i + 1;
    }
    return out;
}

fn poseidon_hasher(n: u32, inputs: [Fp; 6]) -> Fp {
    let POSEIDON_C: [Fp; 455] = [Fp::from(47); 455];
    let POSEIDON_M: [Fp; 49] = [Fp::from(34); 49];

    let t = n + 1;

    let f = 8;
    let p = 57;

    // Constants are padded with zeroes to the maximum value calculated by
    // t * (f + p) = 455, where `t` (number of inputs + 1) is a max of 7.
    // This is done to keep the function generic, as resulting array size depends on `t`
    // and we do not want callers passing down constants.
    // This should be revisited once compiler limitations are gone.

    let c: [Fp; 455] = POSEIDON_C;
    let m: [Fp; 49] = POSEIDON_M;

    let mut state: [Fp; 7] = [Fp::from(0); 7];
    let mut i = 1;
    while i < t {
        state[i as usize] = inputs[(i - 1) as usize];
        i = i + 1;
    }

    let mut r = 0;
    while r < f+p {
        state = ark(n, state, c, r * t);
        state = sbox(n, state, f, p, r);
        state = mix(n, state, m);
        r = r + 1;
    }

    return state[0];
}

#[jolt::provable(stack_size = 100000, memory_size = 100000000)]
fn poseidon(n: u32) -> Fp {
    let mut padded_message: [Fp; 6] = [Fp::from(0); 6];
    let mut sum: Fp = Fp::from(0);
    for i in 0..6 {
        sum = sum + Fp::from(i);
        padded_message[i as usize] = sum;
    }

    let hash: Fp = poseidon_hasher(n, padded_message);

    return hash;
}

// Compact Cert
extern crate alloc;
use alloc::vec::Vec;

// Elliptic Curves
#[derive(Clone, Serialize, Deserialize)]
pub struct Point {
    pub x: Fp,
    pub y: Fp
}

pub const WIDTH: usize = 253;
pub const A: u64 = 526;
pub const B: u64 = 265;

pub fn curve_add(a: &Point, b: &Point) -> Point {
    let m = if a.x != b.x {
        (b.y - a.y) * (b.x - a.x).invert().unwrap()
    } else {
        (Fp::from(3) * a.x * a.x + Fp::from(A)) * (Fp::from(2) * a.y).invert().unwrap()
    };
    let x3 = m * m - a.x - b.x;
    let y3 = m * (a.x - x3) - a.y;
    Point {
        x: x3,
        y: y3
    }
}

pub fn curve_double(a: &Point) -> Point {
    curve_add(a, a)
}

// k_bits in big_endian form
pub fn curve_mul(a: &Point, k_bits: &[bool]) -> Point {
    // Express k using bits
    assert!(k_bits.len() <= WIDTH);
    let mut a_k = a.clone();
    let mut i = 0;
    while !k_bits[i] {
        i += 1;
    }
    i += 1;
    while i < k_bits.len() {
        a_k = curve_double(&a_k);
        if k_bits[i] {
            a_k = curve_add(&a_k, a);
        }
        i += 1;
    }
    a_k
}

#[jolt::provable(stack_size = 100000, memory_size = 100000000)]
fn compact_cert_simple(n: u32) -> Fp {
    let mut p_list = Vec::<Point>::new();
    let mut q_list = Vec::<Point>::new();
    let mut e_list = Vec::<[bool; 253]>::new();
    let mut s_list = Vec::<[bool; 253]>::new();
    // Two multiplications + one addition per signature
    let mut sum: Fp = Fp::from(0);
    for i in 0..n {
        sum = sum + Fp::from((i + 1) as u64);
        p_list.push(Point { x: sum, y: sum });
        q_list.push(Point { x: sum, y: sum });
        e_list.push([true; 253]);
        s_list.push([true; 253]);
    }
    let mut hash: Point = Point { x: Fp::from(0), y: Fp::from(0) };
    for i in 0..n {
        let eq = curve_mul(&q_list[i as usize], &e_list[i as usize]);
        let sp = curve_mul(&p_list[i as usize], &s_list[i as usize]);
        let tmp = curve_add(&eq, &sp);
        hash.x += tmp.x;
        hash.y += tmp.y;
    }
    return hash.x + hash.y;
}