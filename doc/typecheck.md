# Typecheck
* Convert `p_expr` to `expr` with types. Also convert `p_cmd` and `p_fundef`, etc.
* Replace all call-by-references with pointer dereferences.
* Make all implicit type casting explict.
* Replace all unary/binary operations with builtin function calls.

## Call by reference
Function parameters can be declared as call-by-reference. For example:
```
unit f(int & x) {
    x = x + 1;
}
```
It will be converted to the following function before typechecking.
```
unit f(int * x) {
    *x = *x + 1;
}
```
Invocation like `f(a)` will be converted to `f(&a)`.
So when recording function signatures, we not only need the parameters' types,
but also need their calling conventions.