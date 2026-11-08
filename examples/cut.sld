% ?- first_child(tom, C).
?- first_child(tom, C).
  | first_child(X1, C1) :- parent(X1, C1), !.
  | {X1 |-> tom, C1 |-> C}
  ?- parent(tom, C), !.
    | parent(tom, bob).
    | {C |-> bob}
    ?- !.                       @c
      | !
      ?- true.                  {C |-> bob}
    | pruned parent/2 #2        by @c
  | pruned first_child/2 #2     by @c
