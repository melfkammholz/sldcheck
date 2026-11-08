% ?- member(X, [1, 2]), Y is X + 1.
?- member(X, [1, 2]), Y is X + 1.
  | member(X1, [X1|_1]).
  | {X |-> 1, X1 |-> 1, _1 |-> [2]}
  ?- Y is 1 + 1.
    | builtin
    | {Y |-> 2}
    ?- true.                                 {X |-> 1, Y |-> 2}
  | member(X2, [_2|T2]) :- member(X2, T2).
  | {X2 |-> X, _2 |-> 1, T2 |-> [2]}
  ?- member(X, [2]), Y is X + 1.
    | member(X3, [X3|_3]).
    | {X |-> 2, X3 |-> 2, _3 |-> []}
    ?- Y is 2 + 1.
      | builtin
      | {Y |-> 3}
      ?- true.                               {X |-> 2, Y |-> 3}
    | member(X4, [_4|T4]) :- member(X4, T4).
    | {X4 |-> X, _4 |-> 2, T4 |-> []}
    ?- member(X, []), Y is X + 1.
      | no rule
