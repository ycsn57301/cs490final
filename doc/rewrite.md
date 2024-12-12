# Rewrite

## Optimize Return Variables
If a return variable, e.g. `f$r0`, is immediately stored into another variable, then delete `f$r0`. For instance:
```
pvt int f$r0 = ...;
receiver$0 = f$r0;
```
will be merged into:
```
receiver$0 = ...;
```