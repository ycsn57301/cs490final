#!/bin/sh
if [ $# -lt 3 ]; then
    echo "need to specify input file, prover folder and verifier folder"
    echo "example: dune exec -- ou eval --input test/atomic_fft.in.ou --proverdir atomic_fft_prover --verifierdir atomic_fft_verifier"
else
    dune exec -- ou eval --input $1 --proverdir $2 --verifierdir $3
fi