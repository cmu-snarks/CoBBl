/*! Sieve of Eratosthenes

The `bit_vec` crate had this as an example, so I do too, I guess.

Run with

```sh
$ cargo run --release --example sieve -- [max] [count]
```

where max is an optional maximum number below which all primes will be found,
and count is an optional number whose square will be used to display the bottom
primes.

For example,

```sh
$ cargo run --release --example sieve -- 10000000 25
```

will find all primes less than ten million, and print the primes below 625 in a
square 25x25.
!*/

//  Impl notes: If this executable starts segfaulting, `BitSpan::len` might be
//  the culprit. Replace the bare + and - in that function with .saturating_ops
//  and see if that solves it.
//
//  Heisenbugs are weird.

use std::{
	cmp,
	env,
	process,
};

use bitvec::prelude::*;

macro_rules! qprintln {
	($($t:tt)*) => {
		if !cfg!(feature = "testing") {
			println!($($t)*);
		}
	};
}

macro_rules! qprint {
	($($t:tt)*) => {
		if !cfg!(feature = "testing") {
			print!($($t)*);
		}
	};
}

fn main() {
	//  Capture the arguments iterator exactly once.
	let mut args = env::args();
	//  Attempt to parse the first argument as a search ceiling.
	let max: usize = args
		.nth(1)
		.and_then(|arg| arg.parse().ok())
		.unwrap_or(1_000_000);

	//  Allocate and immediately free a `Vec<bool>`, just to prove a point.
	let vec_bool_capa = vec![false; max].capacity();

	//  Prepare a vector for the search space.
	let mut primes: BitVec = BitVec::repeat(true, max);
	let len = primes.len();

	qprintln!(
		"BitVec   [{}]: {} bytes of heap\nVec<bool>[{}]: {} bytes of heap",
		len,
		//  `.capacity()` always returns bits, and we want bytes
		primes.capacity() >> 3,
		len,
		vec_bool_capa,
	);

	//  0 and 1 are not primes.
	primes.set(0, false);
	primes.set(1, false);

	qprintln!("Calculating 1…");
	for num in 2 ..= ((len as f64).sqrt() as usize) {
		//  Adjust the frequency of log statements logarithmically.
		let log = (num as f64).log10();
		if log - log.floor() == 0.0 {
			qprintln!("Calculating {}…", num);
		}
		//  If num is prime, mark all multiples as non-prime.
		if primes[num] {
			//  Start at num * num, because num * (num - 1) was handled in the
			//  previous iteration: (num - 1) * (num - 1 + 1).
			'mul: for factor in num .. {
				let product = num * factor;
				if product >= len {
					break 'mul;
				}
				primes.set(product, false);
			}
		}
	}
	qprintln!("Calculation complete!");
	//  Freeze the vector by permanently borrowing it as an immutable bit-slice.
	let primes = primes.as_bitslice();

	let prime_ct = primes.count_ones();
	let prime_ratio = 100.0 * prime_ct as f64 / len as f64;

	if primes.not_any() {
		qprintln!("There are no primes smaller than {}", len);
		process::exit(0);
	}
	else {
		qprintln!(
			"There are {} primes less than {} ({}%)",
			prime_ct,
			len,
			prime_ratio
		);
	}

	let dim = args.next().and_then(|arg| arg.parse().ok()).unwrap_or(10);

	let limit = cmp::min(dim * dim, len);
	let displayed_primes = &primes[.. limit];
	/* Find the widest number that will be printed, and get its width. To do
	 * this, we:
	 *
	 * - iterate over the bits
	 * - by value
	 * - from the back
	 * - counting up from the end
	 * - seeking the first marked prime
	 * - using `ceil(log10(num))` to find its printed length
	 */
	let cell_width = displayed_primes
		.iter()
		.by_vals()
		.rev()
		.enumerate()
		.find(|(_, bit)| *bit)
		.map(|(idx, _)| ((limit - 1 - idx) as f64).log10().ceil() as usize)
		.expect("Failed to find a prime.");

	let prime_ct = displayed_primes.count_ones();
	let prime_ratio = 100.0 * prime_ct as f64 / limit as f64;
	qprintln!(
		"There are {} primes less than {} ({}%) and they are:",
		prime_ct,
		limit,
		prime_ratio
	);
	'rows: for (row, bits) in displayed_primes.chunks(dim).take(dim).enumerate()
	{
		for (col, bit) in bits.iter().by_vals().enumerate() {
			let idx = row * dim + col;
			if idx >= limit {
				qprintln!();
				break 'rows;
			}
			if bit {
				qprint!("{:>1$} ", idx, cell_width);
			}
			else {
				qprint!("{:^1$} ", "-", cell_width);
			}
		}
		qprintln!();
	}
}

#[cfg(not(feature = "std"))]
compile_error!("This example requires the standard library");
