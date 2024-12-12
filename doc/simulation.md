# Shallow-Sim
* Label all values as compiletime-determined or runtime-determined.

Difference between `expr` and `sexpr`:
* `expr` might contain use-defined function call, while `sexpr` can only have builtin function calls, thus evaluating the latter won't generate any new scmd.

## Enforce Static Scope
We use a list of *function frames* to store the variables defined during execution. The last frame stores the global variables and the first frame stores the local variables in the current function call. Each function frame consists of a list of *section frames* where the first frame corresponds to the inner most section.

When looking up variables, we firstly search the inner most section, then the outer section, etc, util the current function frame has been searched. If still cannot find the variable, the global variables' frame will be searched. By doing so, we can avoid dynamic scope issue.

Here's a counterexample that does not enforce static scope:
If all section frames are piled up without distinction between their belonged functions, then dynamic scope might cause the following program to update the local x instead of the global x:
```
int x = 0;
unit f() {
    x = 1;
    return;
}
unit main() {
    int x = 42;
    f();
    return;
}
```

## Atomic Function Call
During an atomic function's invocation, no history shall be added, and we need to monitor the total computation cost,
and three types of variables that are read/write during the invocation and have longer lifetime than the invocation:
* *pvtW*: the set of updated private variables.
* *pvtR*: the set of accessed private variables.
* *pubR*: the set of accessed public variables and their values when accessed for the first time.

After the function call finished, the entire invocation history is collapsed into one line like `sync x = ..., y = ... then f(...)`. It means firstly assign values to all pubR's variables, then call the function.

In the implementation, the following places are changed:
* `append_to_history` might skip recording when inside atomic invocation
* `sim_expr`'s `Elexpr` case might update pvtR and pubR.
* `sim_cmd`'s `Casgn` case might update pvtW.


## Prover-local
The prover-local function is treated like a sandboxing mechanism.

The prover-local functions are declared as extern functions in the main file. Later the prover will provide their implementations while the verifier does not need to know the details. All dependent values has to be passed in as arguments, i.e., the prover-local function's body should not refer to any external variables. The prover-local function eventually returns a value which will be sent/revealed as public/private value.
We enforce such restriction because during shallow-simulation, we can not know the details within the prover-local function's body, so we won't know which variable is read/written. The prover-local function behaves like a blackbox during shallow-simulation, which makes the cutting almost impossible. So we can only regulate the information flow in and out at the function calls' boundary.

What if an argument contains pointer? There are two choices:
1. Forbid such case. Sounds reasonable, but makes the paper weak and might influence the performance. Because now if we need to read/write some indexes of a big array, we have to pass in the entire array instead of its pointer.
2. Pointer swizzling. Follow L0 pointers and recursively label all lvalues as R&W. A more optimized approach is following C++ or rust's approach by marking a reference as read-only or read-and-write, but it takes more time and need to change the type system. This feature is also not related to this paper's essence so we should not spend too much time on it. We probably will implement it as a future update.



# Deep-Sim

## Runtime(L2)
The only way to go from L0 or L1 to L2 is by invoking random functions.