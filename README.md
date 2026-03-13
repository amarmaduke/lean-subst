# Lean Substitution Library (lean-subst)

Inspired heavily by the work on Autosubst [[1]](https://doi.org/10.1007/978-3-319-22102-1_24) [[2]](https://dl.acm.org/doi/10.1145/3293880.3294101), this library gives a framework for handling De Bruijn substitution for non-indexed syntax.

Features:
1. Heterogenous simultaneous substitutions (like the original Autosubst in Rocq)
2. Variables can track additional data (because renamings embed into substitutions)
3. Annotations for `simp` and `grind` enabling automation of the convergent rewriting system described in the Autosubst literature

Variables tracking additional data is accomplished by treating substitutions as sequences of "substitution actions":
```lean
inductive Action T where
| su : T -> Action T
| re : Nat -> Action T

Subst T := Nat -> Action T
```
The `su` constructor encodes a genuine replacement for a variable at the right index with a term. The `re` constructor encodes a renaming where a variable constructor's annotated data is preserved and only its index is modified.

TODO:
1. Generalization to vector substitutions
2. Support for well-scoped De Bruijn
1. Automatic derivation of substitution definitions, lemmas and typeclasses

# Usage

Add the following to your `lakefile.toml`:

```toml
[[require]]
name = "lean-subst"
scope = "amarmaduke"
git = "https://github.com/amarmaduke/lean-subst"
rev = "main"
```

Change `rev` to a release tag or pinned commit as desired, then run `lake update`.

Syntax must be non-indexed, see "Examples" for the various requirements needed to properly set up an inductive type encoding syntax.

Other non-trivial uses of this library are available here:
1. [A mechanization of the metatheory of STLC](https://github.com/amarmaduke/lean-stlc)
2. [A mechanization of the metatheory of System F](https://github.com/amarmaduke/lean-sysf)