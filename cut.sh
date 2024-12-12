#!/bin/sh
if [ $# -eq 0 ]; then
    echo "need to specify .ou program"
    echo "example: dune exec -- ou cut --proto test/atomic_fft.ou --noc 3"
elif [ $# -eq 1 ]; then
    dune exec -- ou cut --proto $1 --noc 1
else
    dune exec -- ou cut --proto $1 --noc $2
fi