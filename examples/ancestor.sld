% ?- ancestor(tom, W).
?- ancestor(tom, W).
  | ancestor(X1, Y1) :- parent(X1, Y1).
  | {X1 |-> tom, Y1 |-> W}
  ?- parent(tom, W).
    | parent(tom, bob).
    | {W |-> bob}
    ?- true.                                 {W |-> bob}
  | ancestor(X2, Y2) :- parent(X2, Z2), ancestor(Z2, Y2).
  | {X2 |-> tom, Y2 |-> W}
  ?- parent(tom, Z2), ancestor(Z2, W).
    | parent(tom, bob).
    | {Z2 |-> bob}
    ?- ancestor(bob, W).
      | ancestor(X3, Y3) :- parent(X3, Y3).
      | {X3 |-> bob, Y3 |-> W}
      ?- parent(bob, W).
        | parent(bob, ann).
        | {W |-> ann}
        ?- true.                             {W |-> ann}
        | parent(bob, pat).
        | {W |-> pat}
        ?- true.                             {W |-> pat}
      | ancestor(X4, Y4) :- parent(X4, Z4), ancestor(Z4, Y4).
      | {X4 |-> bob, Y4 |-> W}
      ?- parent(bob, Z4), ancestor(Z4, W).
        | parent(bob, ann).
        | {Z4 |-> ann}
        ?- ancestor(ann, W).
          | ancestor(X5, Y5) :- parent(X5, Y5).
          | {X5 |-> ann, Y5 |-> W}
          ?- parent(ann, W).
            | no rule
          | ancestor(X6, Y6) :- parent(X6, Z6), ancestor(Z6, Y6).
          | {X6 |-> ann, Y6 |-> W}
          ?- parent(ann, Z6), ancestor(Z6, W).
            | fails
        | parent(bob, pat).
        | {Z4 |-> pat}
        ?- ancestor(pat, W).
          | ancestor(X7, Y7) :- parent(X7, Y7).
          | {X7 |-> pat, Y7 |-> W}
          ?- parent(pat, W).
            | no rule
          | ancestor(X8, Y8) :- parent(X8, Z8), ancestor(Z8, Y8).
          | {X8 |-> pat, Y8 |-> W}
          ?- parent(pat, Z8), ancestor(Z8, W).
            | no rule
