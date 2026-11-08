% ?- d(X, Y).   The cut commits to b(1) but not to a single c: both answers stay.
?- d(X, Y).
  | d(X1, Y1) :- b(X1), !, c(Y1).
  | {X1 |-> X, Y1 |-> Y}
  ?- b(X), !, c(Y).
    | b(1).
    | {X |-> 1}
    ?- !, c(Y).                       @c
      | !
      ?- c(Y).
        | c(2).
        | {Y |-> 2}
        ?- true.                      {X |-> 1, Y |-> 2}
        | c(3).
        | {Y |-> 3}
        ?- true.                      {X |-> 1, Y |-> 3}
    | pruned b/1 #2                   by @c
    | pruned b/1 #3                   by @c
