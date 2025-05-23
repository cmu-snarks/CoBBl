use serde::{Serialize, Deserialize};
use ff::Field;
use crate::field::Fp;
use rug::Integer;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
pub fn curve_mul(a: &Point, mut k: Integer) -> Point {
    assert!(k != Integer::from(0));
    // Express k using bits
    let mut k_bits = Vec::new();
    while k != Integer::from(0) {
        k_bits.insert(0, k.clone() % 2 == Integer::from(1));
        k /= 2;
    }

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