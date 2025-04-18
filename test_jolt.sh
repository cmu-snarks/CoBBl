#!/bin/bash
rustup install nightly-2024-09-01 &&
cd jolt && RAYON_NUM_THREADS=1 cargo +nightly-2024-09-01 run --release -p multi-function > ../zok_tests/raw/jolt_result.raw