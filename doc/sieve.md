# Statements

## SSA
Only SSA style of assignment is permitted in SIEVE IR. So we firstly need to convert all compound expressions into SSA sequences. For instance, `(a + b) * c` will be converted to `$4 <- $1 + $2; $5 <- $4 * $3;`.

Also, all assignments in ou-lang will be changed: its LHS should be replaced by a new wire, and all occurrences of this variable/lvalue in the future should be replaced by this wire. For instance, `a[0] = 42; a[0] = a[0] + 1; x = a[0] * 2;` becomes `$10 <- 42; $11 <- $10 + 1; $12 <- $11 * 2;`.
It is easy to do such conversion for scmd (when private accessible RAM is not used) as we know the location of each lvalue/variable.
But when inside a function body, it is no longer possible to infer the actual location, as the location might depend on the function's arguments or previous computations. For example, in `a[i] = 42; x = a[j];`, we won't know if `i` and `j` point to the same location. So for simplicity, no array indexing is allowed to appear in the LHS of atomic function's body.
We still allow variables or struct's fields to be assigned with, as it is easy to infer their locations.
For example, `s3 = {.re = s1.re + s2.re, .im = s1.im + s2.im};` becomes `$5 = $1 + $3; $6 = $2 + $4;` if `$1` and `$2`, `$3` and `$4`, `$5` and `$6` store s1, s2 and s3 respectively.

## (Future work) For-loop
SIEVE IR only supports a very limited for-loop, and its "iterator-expression" is very restricted. So we can not easily convert an arbitrary while-loop to it. Instead, we probably should add a for-loop into the ou-lang?
The for loop has an out-list, which encapsulates all side-effects within the loop. We need to convert the command's live-out to this out-list.

## Switch-case
I do not understand the switch-case statement.


# Pointers
SIEVE IR does not have pointer. Fortunately, the pointers in ou-lang are all public.
So we will use a 


# Input stream
SIEVE IR does not have global variables, instead it uses two input streams: `@short_witness` and `@instance`. We will use `@short_witness` as live-in variables and probably ignore `@instance`.
Another problem is that each value in these streams can only be read once. So we will use some temporary wires to firstly consume these streams, then do all computations based on these wires.
There's another benefit: we no longer need to fill in the `n_instance` and `n_s_witness` of functions definitions.


# Functions
SIEVE IR only allows a very restricted form of function, i.e., the function corresponds to a fixed circuit.
We need to define a notion of **well-formedness** to match with SIEVE IR's function. All atomic functions must be well-formed as following:

* To make the checking easier, atomic functions can only call atomic functions (for SIEVE IR specifically). So we just need to check that all atomic functions are well-formed. Otherwise, we have to go over all functions that's ever invoked by an atomic function.
* Recursion is not allowed in atomic functions.
* (Future work) There's no way to read or update global variables within a function. Actually, it seems the function's body has an isolated scope like sandbox, so there's no way to access any wire outside this scope. So to access the global variables, we have to define any function with side-effects in a monad way: we convert the live-in to the function's in-list and convert the live-out to the function's out-list. To make sure such conversion works, the live-in and live-out must be the same in any invocation.

