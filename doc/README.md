# Introduction
DZKP (Distributed Zero-Knowledge Proof) is a C-like language with privacy features. A DZKP program can be compiled to a zero-knowledge proof protocol written in DZKP-IR, then sliced into multiple separate protocols, eventually compiled to various circuit implementations like [EMP](https://github.com/emp-toolkit/emp-zk), [SIEVE IR](https://hackmd.io/@danib31/BkP9HBp2L) or [ZKsnark](https://github.com/scipr-lab/libsnark).

# Workflow
Firstly, The main verifier server processes the source code:
```
DZKP source code -> [parse] [typecheck] [del_public_from_su_env] [shallow-sim] ->
DZKP-IR -> [optimize_return_variables] [live variable analysis] [slice] ->
DZKP-IR fragements
```
Then all fragments will be sent to the prover:
```
DZKP-IR fragments -> [var-eval] -> pvt-vals list
```
And each verifier will receive one fragment:
```
DZKP-IR fragment -> [deep-sim] -> DZKP-SEQ -> [EMP-gen / ZKsnark-gen] -> ZK circuit
```
Eventually, each verifier will run its circuit by interacting with prover's `pvt-vals`.

# Details
The following documents explain the language's syntax, semantics and implementation in details.

[Language](language.md)

[Typecheck](typecheck.md)

[Simulation](simulation.md)

[Rewrite](rewrite.md)

[Slicer](slicer.md)