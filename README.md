# How to build
1. Install opam and ocaml 4.14.0
```shell
# after install opam
$ opam init
$ opam switch create 4.14.0
$ opam switch 4.14.0
$ eval $(opam env)
```
2. Install dependent ocaml packages
```shell
$ opam install menhir dune fmt logs alcotest
```
3. Install dependent python packages (no longer needed)
```shell
$ python3 -m venv pyenv
$ source pyenv/bin/activate
```
4. Install OPB solver.
This step is necessary to partition a ZK protocol into multiple parts.
We have tested on Gurobi-10.0:
[Gurobi](https://www.gurobi.com/downloads/gurobi-software/)
5. Build
```shell
$ dune build
```

# How to use (EMP)
The verifier coordinator runs:
```shell
$ dune exec -- ou cut --proto examples/merkle.ou --noc 3
```
The generated EMP files will be output to two folders `merkle_prover` and `merkle_verifier`.

The prover coordinator then evaluates dependent variables using initial secret:
```shell
$ dune exec -- ou eval --input examples/merkle.in.ou --proverdir merkle_prover --verifierdir merkle_verifier
```
Both prover and verifier coordinators then compile their own code in two directories.
Please follow this [guide](https://github.com/emp-toolkit/emp-zk) to install the dependent libraries before compiling the generated code.
```shell
# enter merkle_prover/ and merkle_verifier/ and run
$ make
```
Both coordinators will obtain three executables: `part0`, `part1` and `part2`.
They then distribute these executables to individual provers and verifiers respectively.
Each pair of prover and verifier run the same pair of executables on the same port. For example, the first pair both run the following command in a folder containing a `data` directory:
```shell
$ ./part0 12345
```
Note that the generated code assumes the executables from both sides are run in the same machine. But you can let them run on different machines by changing the communicating IP addresses in `part*.cpp`.

# How to use (ZoKrates)
TODO

# Syntax Highlight
If you are using vscode, you can enable syntax highlight for all `.ou` files by moving the `ou-vscode-syntax` directory into `~/.vscode/extensions/` if you use Linux or `%USERPROFILE%\.vscode\extensions` if you use Windows.
