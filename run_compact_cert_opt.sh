#!/bin/bash
max_reveal=545
echo "" > zok_tests/compact_cert_field/opt &&
cp zok_tests/benchmarks/compact_cert/data/$max_reveal.input zok_tests/benchmarks/compact_cert/compact_cert.input &&
cp zok_tests/benchmarks/compact_cert/data/$max_reveal.witness zok_tests/benchmarks/compact_cert/compact_cert.witness &&
cd circ_blocks &&
echo "OPT 0" >> ../zok_tests/compact_cert_field/opt &&
target/release/examples/zxc compact_cert/compact_cert --inline_spartan --opt_level=0 | sed -n -e's/Compiler time: //p' -e 's/  \* SNARK::prove //p' -e 's/  \* SNARK::verify //p' -e 's/Total Proof Size: //p' >> ../zok_tests/compact_cert_field/opt &&
echo "OPT 1" >> ../zok_tests/compact_cert_field/opt &&
target/release/examples/zxc compact_cert/compact_cert --inline_spartan --opt_level=1 | sed -n -e's/Compiler time: //p' -e 's/  \* SNARK::prove //p' -e 's/  \* SNARK::verify //p' -e 's/Total Proof Size: //p' >> ../zok_tests/compact_cert_field/opt &&
echo "OPT 2" >> ../zok_tests/compact_cert_field/opt &&
target/release/examples/zxc compact_cert/compact_cert --inline_spartan --opt_level=2 | sed -n -e's/Compiler time: //p' -e 's/  \* SNARK::prove //p' -e 's/  \* SNARK::verify //p' -e 's/Total Proof Size: //p' >> ../zok_tests/compact_cert_field/opt &&
echo "OPT 3" >> ../zok_tests/compact_cert_field/opt &&
target/release/examples/zxc compact_cert/compact_cert --inline_spartan --opt_level=3 | sed -n -e's/Compiler time: //p' -e 's/  \* SNARK::prove //p' -e 's/  \* SNARK::verify //p' -e 's/Total Proof Size: //p' >> ../zok_tests/compact_cert_field/opt &&
cd ..