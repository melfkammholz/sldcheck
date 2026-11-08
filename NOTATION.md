# The SLD tree notation

A text format for SLD trees of Prolog programs, as drawn by hand: nodes are goals, steps are resolution steps labelled with the renamed clause and the unifier. [sldcheck](README.md) reads it and checks the tree against a program.

```
?- max(3, 5, M).
  | max(X1, Y1, Y1) :- X1 =< Y1, !.
  | {X1 |-> 3, Y1 |-> 5, M |-> 5}
  ?- 3 =< 5, !.
    | builtin
    ?- !.                      @c
      | !
      ?- true.                 {M |-> 5}
  | pruned max/3 #2            by @c
```

for the program

```prolog
max(X, Y, Y) :- X =< Y, !.
max(X, _, X).
```

## Structure

The tree is written by indentation, with spaces (not tabs).

- A line starting with `?-` is a **node**: a goal, ending with a dot.
- Lines starting with `|` are a **step** below the node: the edge to a child, or a statement about why there is none.
- The steps of a node are in one column, to the right of the node. A step is followed by its **child**, which is in the same column as the step. The child's own steps are further to the right.
- `%` starts a comment, and `/* ... */` is a comment too. Comments and blank lines can be anywhere between tokens.

Goals and rules are ordinary Prolog. The one difference is that `|` is not an operator here (write a disjunction with `;`): a goal whose end dot is missing would otherwise run into the `|` of the next step.

## Nodes

```
?- goal.            @name       {X |-> t, ...}
```

- The **goal** is a Prolog term, usually a conjunction. The goal `true` is the empty goal: the query is proven there.
- The optional **name** `@name` (letters, digits, underscore) is how other parts of the file refer to the node. Names are unique in the file.
- An optional **answer** `{...}` may follow, at a proven node (goal `true`) only. It is the composition of the substitutions on the branch, restricted to the variables of the query, without the bindings that do nothing. The checker verifies it. Without an answer you get a warning (an error with `--require-answers`).

## Steps

| Step | Meaning |
|---|---|
| `\| rule.` | resolution with this clause, renamed apart |
| `\| {X \|-> t, ...}` | the unifier of this step, on its own line below the rule or `builtin` |
| `\| builtin` | a built-in was evaluated (`true`, `fail`, `=`, `\=`, `==`, `\==`, `is`, `<`, `>`, `=<`, `>=`, `=:=`, `=\=`) |
| `\| !` | the cut was selected |
| `\| \+ @t` | negation as failure; `@t` is the tree of the negated goal, and it has no success |
| `\| pruned p/n #k by @c` | alternative clause `k` of `p/n` is not tried, because the cut in node `@c` removed it |
| `\| no rule` | no clause head unifies with the selected literal |
| `\| builtin fails` | a built-in test is false |
| `\| \+ @t fails` | the tree `@t` has a success, so the negation fails |
| `\| fails` | the branch fails, reason not stated (accepted wherever a reason would be) |
| `@name` | in place of a child: the rest of the tree is written separately (see below) |

A node whose goal is not `true` must end in one of the steps that continue the tree, or in a failure. A failure has to say so: a node with no steps is an error.

### Rules and unifiers

- The rule is the clause of the program with its variables renamed to fresh ones. It must not use a variable that already occurs earlier on the path (the query, earlier rules, the goal). Anonymous variables are not allowed anywhere (`_` cannot be bound by a substitution): rename them, for instance `_1`.
- The unifier is a most general unifier of the selected literal and the head of the rule. Any most general unifier is accepted, whichever way variables are bound to each other. It binds only variables of those two terms.
- The goal below the step is the body of the rule followed by the rest of the goal, with the unifier applied.
- A step for a program predicate is chosen by the leftmost selection rule. Alternatives are listed in program order: the clause number `k` in `pruned p/n #k` counts the clauses of `p/n`, from 1.

### The cut

`!` is the selected literal at a node, and the node has one step, `!`. The cut removes the alternatives of the node that called the clause containing it, and of every node between that one and the cut. Each of these alternatives is written as a `pruned` entry, at the place in the order where its branch would have been, and names the cut that is responsible. If several cuts on the branch reach an alternative, the first one in the tree is responsible. Only alternatives that would have unified are listed, and an alternative that is pruned is not drawn.

### Negation

`\+ G` is a node with one step: `\+ @t`, where `@t` is the root of a separate tree for `G` (see below). If `G` has no solution, the step is followed by the rest of the goal. If it has one, the step is `\+ @t fails` and there is nothing below. Cuts inside the tree of `G` do not leave it.

## Several trees

The first `?-` at column 1 is the query. Other trees at column 1 are written separately and referred to by name. Their roots must be named, and each is referred to exactly once. A tree is either

- **the tree of a negation**, referred to by `| \+ @t`. It is a separate query for the negated goal, and it starts with that goal.
- **a part of the tree** that refers to it, written by `@name` in place of a child. This keeps deep trees readable:

  ```
  ?- ancestor(tom, W).
    | ancestor(X2, Y2) :- parent(X2, Z2), ancestor(Z2, Y2).
    | {X2 |-> tom, Y2 |-> W}
    @recursive

  ?- parent(tom, Z2), ancestor(Z2, W).         @recursive
    | parent(tom, bob).
    | {Z2 |-> bob}
    @bob
  ```

  The reference is aligned with its step, as a child node would be. The referenced tree is part of the tree that refers to it: renaming, cut and answers work exactly as if it were written in place. A tree cannot contain itself.

`examples/ancestor-split.sld` is `examples/ancestor.sld` written this way.

## Order

The steps of a node are in the order Prolog tries them: the clauses in program order, with `pruned` entries where the pruned alternative would have been. A tree that has the right branches in another order has an error.
