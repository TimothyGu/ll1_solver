LL(1) solver
============

This program creates an LL(1) parse table given a context-free grammar. Given
the following BNF grammar in standard input:

```
A :== yCz
B :== ε | zyA
C :== yBCC | ε | wz
```

It prints out

```
nullable map:
A -> false
B -> true
C -> true
first set map:
A -> [y]
B -> [z]
C -> [wy]
follow set map:
A -> [$wyz]
B -> [wyz]
C -> [wyz]
table:
(A,y) -> [yCz]
(B,w) -> [ε]
(B,y) -> [ε]
(B,z) -> [ε, zyA]
(C,w) -> [ε, wz]
(C,y) -> [ε, yBCC]
(C,z) -> [ε]
```

The input format specifically follows that given by
http://ll1academy.cs.ucla.edu/.

License
-------

`main.ml` and `solver.ml` are licensed under the MIT license. However,
`nsplit.ml` was taken from [Batteries
Included](http://batteries.forge.ocamlcore.org/) and thus licensed under GNU
LGPL 2.1 or above.
