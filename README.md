# sldcheck

A checker for SLD trees of Prolog programs, written in Haskell.

SLD trees show how Prolog answers a query: each node is a goal, each step is a resolution with a renamed clause and its unifier, and the cut and negation as failure change the shape of the tree. `sldcheck` reads such a tree in a [small text notation](NOTATION.md) and checks it against the Prolog program. It reports every problem it can find, each with a stable code, a position and an explanation: wrong clauses, wrong unifiers, missing or superfluous branches, mistakes with the cut and with negation, wrong answers.

It was written to check the SLD trees students draw in a course on declarative programming. It has no notion of a grade: a tree is correct, or the diagnostics say what is not.

## Build

You need GHC and cabal (GHC 9.10 is what it is tested with).

```
cabal build
cabal run sldcheck -- TREE.sld PROGRAM.pl
cabal install          # puts sldcheck on your PATH
```

## Example

The program ([examples/cut.pl](examples/cut.pl)):

```prolog
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).

first_child(X, C) :- parent(X, C), !.
first_child(_, none).
```

The tree for `?- first_child(tom, C).` ([examples/cut.sld](examples/cut.sld)). The cut commits to `parent(tom, bob)` and to the first clause, so the other alternatives are pruned, and each says which cut removed it:

```
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
```

```
$ sldcheck examples/cut.sld examples/cut.pl
examples/cut.sld: no problems found
```

Without the last line, the second clause is neither drawn nor pruned:

```
cut-broken.sld:2:1: error[E022]: clause 2 of first_child/2 unifies with `first_child(tom, C)` but is neither drawn nor pruned: `first_child(_, none)`
cut-broken.sld: 1 error, 0 warnings, 0 notes
```

[examples/ancestor-broken.sld](examples/ancestor-broken.sld) is a larger tree with five marked mistakes. More correct trees are in [examples/](examples/): recursion, lists and arithmetic, the cut between two literals, negation, and a big tree split into parts.

## Usage

```
sldcheck TREE.sld PROGRAM.pl [--json] [--require-answers]
```

- `--json` prints the diagnostics as a JSON array (`severity`, `code`, `line`, `column`, `message`).
- `--require-answers` makes a proven node without its answer an error instead of a warning.
- Exit status: 0 no errors (warnings may be printed), 1 the tree has errors, 2 bad input, including syntax errors.

The program is read with its `op/3` directives, and the tree with the resulting operators.

## How it checks

Every node is checked against what is correct *from that node as drawn*, not against an ideal tree. A mistake in one step neither hides nor causes mistakes elsewhere: below a wrong goal, the checker goes on as if the goal had been right. What it covers:

- **Resolution**: the rule is a renamed copy of a clause of the right predicate, renamed apart from everything used before; the substitution is a most general unifier; the goal below is the resolvent.
- **Branches**: leftmost selection and program order; every alternative whose head unifies is drawn or pruned, once; a branch that ends says why, and the reason is true.
- **The cut**: which alternatives it removes, and which cut is responsible for each (`pruned ... by @c`).
- **Negation as failure**, with its own tree for the negated goal.
- **Built-ins**: `is`, the comparisons, `=`, `\=`, `==`, `\==`, `true`, `fail`.
- **Answers**: the answer stated at a proven node is the composition of the substitutions on its branch, restricted to the query variables.

An independent solver in the library (`SLDCheck.Solve`, with cut and negation) decides whether a negated goal has a solution. If the checker finds nothing wrong, it also compares the tree's answers with the solver's, as a safety net (E099).

## Limitations

- Control constructs other than the cut and `\+` are not supported: `;`, `->`, `*->`, `call/N`, `findall/3` and the like. A node that selects one gets warning W001 and is not checked further. (In trees, `|` is not an operator; write `;`.)
- Infinite branches are not supported. There is no way to mark an unfinished branch, so every branch of a tree must end.
- A built-in that raises an error (for example `X > 1` with `X` unbound) gets warning W003; an SLD tree cannot show an error, so the node is not checked further.
- A call of a predicate without clauses counts as a failure (`no rule`), with warning W002. A real Prolog would raise an existence error.
- A negated goal whose truth the reference solver cannot decide within its step limit is not checked (W006).
- There is no weighting of mistakes: the tree is correct or the diagnostics say what is not.

## Diagnostics

| Code | Meaning |
|---|---|
| E001 | a name is used twice |
| E002 | a referenced name does not exist |
| E003, E004, E005 | a tree after the first is referenced by nothing, has no name, or is used twice |
| E006 | an answer on a node that is not proven |
| E007, E008 | references between trees: a tree contains itself, or is used both as a part and as the tree of a negation |
| E010 | anonymous variable `_` in a goal or rule |
| E011 | the rule is not a renamed copy of a clause |
| E012 | the rule is not renamed apart from earlier variables |
| E013 | the rule is for another predicate than the selected literal |
| E014, E015, E016, E017, E018 | the substitution: does not unify, is no unifier, is not most general, binds foreign variables, binds a variable twice |
| E020 | wrong goal below a step (not the resolvent) |
| E021 | clauses not in program order |
| E022, E023 | an alternative is missing, or used twice |
| E024 | a step that does not fit the selected literal |
| E025, E026 | a branch ends without a reason, or with a wrong one |
| E027 | steps below a proven node |
| E028 | a substitution where there should be none |
| E029 | a step without its node |
| E030 | `pruned`, but no cut reaches that alternative |
| E031 | `pruned`, but by the wrong cut |
| E032 | `pruned` names something that is not an alternative |
| E033 | an alternative is drawn although a cut removes it |
| E040, E041, E042 | negation: tree for another goal, wrong outcome, outcome and tree disagree |
| E050, E051 | wrong answer, missing answer (with `--require-answers`) |
| E099 | the checker and the reference solver disagree: a bug |
| W001..W006, I001 | unsupported construct, unknown predicate, built-in raises an error, missing answer, redundant binding, undecidable negation, solver stopped early |

## Layout

```
src/SLDCheck/Prolog.hs      terms: syntax, operators, parser, printer
src/SLDCheck/Logic.hs       substitutions, unification, built-ins, program index
src/SLDCheck/Solve.hs       reference solver (cut, negation)
src/SLDCheck/Tree.hs        the abstract syntax of a tree
src/SLDCheck/Notation.hs    parser for the notation
src/SLDCheck/Expand.hs      replaces references between trees by the trees
src/SLDCheck/Check.hs       the checker
src/SLDCheck/Diagnostic.hs  diagnostics, text and JSON
app/Main.hs                 the command line
test/Spec.hs                cases, examples, comparison with swipl
examples/                   programs and trees
```

## Tests

```
cabal test
```

Run it from the package directory. It checks a set of correct and deliberately broken trees, every file in `examples/`, and compares the reference solver with SWI-Prolog on a dozen queries (skipped if `swipl` is not installed).

## Use of AI

This project was developed with an AI coding assistant. The AI wrote the code, the tests and the documentation in conversation with the author, who made the design decisions. The checker is tested on correct and deliberately broken example trees, and its reference solver is compared with SWI-Prolog, but it may still contain mistakes. Do not rely on it as the only judge of someone's work.

## License

BSD 3-Clause, see [LICENSE](LICENSE).
