# DZKP Language

## Datatype

### Integer

### Float

### Array

### Struct

## Expression

## Command

## Function

## Prover-local
The users can mix plocal with private and public. They can even define a struct containing fields from all these domains.
When generating emp code, we will generate two different struct definition for prover and verifier: the verifier's version won't contain any plocal datatype at all.

We have to reproduce all commits on verifier side to match with the prover's commits. We utilize C's comma operation to run these commits. For example, `commit(reveal(commit(x + 1) + commit(y)))` becomes `Integer(32, (Integer(32, x + 1, ALICE) + Integer(32, y, ALICE)).reveal(int)(ALICE), ALICE)` for prover, and `Integer(32, (Integer(32, 0, ALICE), Integer(32, 0, ALICE), 0), ALICE)` for verifier.

### Plocal function
* The branching condition can be plc bool or pub bool.
* Can not R/W global avriables.
* Can only call plocal functions.
* Can not commit nor create any pvt value.
* Can not pass in pointer nor pvt.
A consequence is: Can not return anything containing pvt. (should better make sure it also can not return anything containing pointer, but that will cause runtime error anyway)
In general, can not do anything requiring the verifier's action, can not R/W any outside state, can only return plc values.
By enforcing the above restrictions, we can keep the plocal's invocation local and make sure it's pure.
We want it to be pure because we can not run plocal functions during shallow-sim, so we can not analyze its live-in/live-out.

# DZKP-IR Language