# Ongoing
* Support plocal functions
* Make all dependent variables global in the generated EMP code (so that we can initialize them in a separate function)

# TODO
## High Priority
* Better support for nested data type
* Allow call result to be stored in general lvalue.
* Add seclvl to pointer
* Sandbox/plocal functions should only return K1/K2 values? And should not return a pointer.
* Check all lvalue's klvl <= its value's klvl
* Generate SIEVE IR (?)
* Serialize data of any type to a sequence of primitive data, for consistency check (?)
* Consider ram private access when computing cost
* Add `pub_init`, and rename `init` into `pvt_init`
## Low Priority
* Skip analysis if noc = 1
* Only store necessary values in ssim's stack
* Allow define uninitialized variable
* Attach a different kind type to alias
* Add string & char
* Try allow pointer to be k1/k2, and use seclvl instead of klvl in the meta of lexpr and lvalue.
* Add type info into value
* Merge the common part of ssim and dsim
* Add .mli files
* Probably no need to generate default value for plc
* Define a config file to specify coordinator/provers/verifiers, companying with a script to run the cut/eval/prove
* Support `pvt << pub` and `pub >> pvt`
* Unit tests
* Support constant
* Add p_typ into type system. This could allow array with variable size.
* Add command-line arguments to control which debugging info to be printed
* Use pretty-printer instead of string_of to display AST
* Change function return declaration to go-lang style (to support SIEVE IR style of out wires)
* Split primitive type and compound type
* Unify the constant in expr, sexpr and value
* Let builtin's cost be based on arguments or arguments' types
* To support SHA256, we may need to support C-style use of pointer, or introduce Rust-style slice.
* The cost could somehow be smaller by treating immutable variables in a special way
* Define `expr_init` for variable definition. Eliminate array_init from normal expr.
* Document how ILP works
* Add ln, sqrt, exp
* Maybe define a new `value` type without including array nor struct.
* We probably could derive all variables' types automatically like ML.

# Finished
* Split SEvalue into SEint, SEfloat, etc. (So SEvalue Varray and SEarrayinit will be merged)
* Add a three-color graph example.
* Use logging system [Logs](https://github.com/dbuenzli/logs)
* Fix issue in record_K0R and record_K1K2R
* Uniform array and zkram
* Add plc domain
* Change function call's syntax
* Make print polymorphic
* Support blackbox
* Add reveal and rand
* Default use noc = 1
* Add K1/K2 into dsim
* Update live analysis
* emp-gen
* Create two versions for each builtin function: deep-sim and shallow-sim
* Add klvl into lexpr's meta.
* Allow symbolic public value in shallow-sim.
* Package all EMP files, including the marshal file together
* Add meta info (type, line number, etc) to AST
* Define our own Location module (because the OCaml's Location module is unstable)
* Support plocal function
* Separate EMPgen for prover and verifier
* Separate privately and publicly accessable array
* Skip adding pubR when computing arguments
* Support assertion on declassified bit
* Generate emp file for prover side
* Treat builtin and normal function calls differently
* Split common fundef & sudef and protocol fragment into two files
* Delete external definitions
* Evaluate edge variables at prover side
* Generate function declarations and struct declarations for emp program
* Generate emp program
* Use command line options to determine prover/verifier side
* No longer print then parse sliced ou protocols. Instead, both slice and generate circuit at the coordinator side.
* Change array init style to match up C++ std::array.
* Add symbolic value `svalue` which will be used to store public and private info during shallow-sim
* Separate SCcall's pvtR and pvtW out as a standalone hashtbl
* Separate alias depth out as a standalone hashtbl
* Print sliced ou protocol
* Interact with Python ILP script within OCaml
* Record each builtin function's cost
* No longer extract pvt info from sexpr
* Convert binary and unary expressions into builtin function calls
* Annotate var with its type in lexpr and slexpr
* Refactor builtin module to separate implementation and signature.