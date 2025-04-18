#!/bin/bash
reveals=( 173 205 248 308 397 545 842 1729 )
percs=( 0.6 0.65 0.7 0.75 0.8 0.85 0.9 0.95 )
sizes=( 277119 328347 397172 493206 635705 872631 1348088 2768055 )
echo '' > zok_tests/compact_cert_field/output &&
for (( i=0; i<${#reveals[@]}; ++i ))
do
  reveal=${reveals[$i]}
  perc=${percs[$i]}
  size=${sizes[$i]}
  cp zok_tests/benchmarks/compact_cert/data/$reveal.input zok_tests/benchmarks/compact_cert/compact_cert.input &&
  cp zok_tests/benchmarks/compact_cert/data/$reveal.witness zok_tests/benchmarks/compact_cert/compact_cert.witness &&
  echo "" >> zok_tests/compact_cert_field/output &&
  echo "--" >> zok_tests/compact_cert_field/output &&
  echo "$perc" >> zok_tests/compact_cert_field/output &&
  echo "$reveal" >> zok_tests/compact_cert_field/output &&
  echo "$size" >> zok_tests/compact_cert_field/output &&
  echo "--" >> zok_tests/compact_cert_field/output &&
  cd circ_blocks &&
  target/release/examples/zxc compact_cert/compact_cert --inline_spartan | sed -n -e's/Compiler time: //p' -e 's/  \* SNARK::prove //p' -e 's/  \* SNARK::verify //p' -e 's/Total Proof Size: //p' >> ../zok_tests/compact_cert_field/output &&
  cd ..
done