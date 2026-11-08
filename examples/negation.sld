% ?- parent(tom, C), \+ has_child(C).
?- parent(tom, C), \+ has_child(C).
  | parent(tom, bob).
  | {C |-> bob}
  ?- \+ has_child(bob).
    | \+ @t1 fails
  | parent(tom, liz).
  | {C |-> liz}
  ?- \+ has_child(liz).
    | \+ @t2
    ?- true.                    {C |-> liz}

?- has_child(bob).              @t1
  | has_child(X1) :- parent(X1, _1), !.
  | {X1 |-> bob}
  ?- parent(bob, _1), !.
    | parent(bob, ann).
    | {_1 |-> ann}
    ?- !.                       @c1
      | !
      ?- true.                  {}

?- has_child(liz).              @t2
  | has_child(X2) :- parent(X2, _2), !.
  | {X2 |-> liz}
  ?- parent(liz, _2), !.
    | no rule
