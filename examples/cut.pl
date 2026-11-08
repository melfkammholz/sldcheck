parent(tom, bob).              % 1
parent(tom, liz).              % 2
parent(bob, ann).              % 3

first_child(X, C) :- parent(X, C), !.     % 1
first_child(_, none).                      % 2

has_child(X) :- parent(X, _), !.
