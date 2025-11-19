# Lean Substitution Library (lean-subst)

Inspired heavily by the work on Autosubst ([1])[https://doi.org/10.1007/978-3-319-22102-1_24] ([2])[https://dl.acm.org/doi/10.1145/3293880.3294101], this library gives a framework for handling De Bruijn substitution for non-indexed single-sorted syntax. Other Autosubst inspired systems supported multi-sorted syntax by way of multi-sorted substitutions (i.e., `t[σ;τ]` substitutes for the term and type variables via two separate substitutions). This library instead allows variables to be annotated with extra data. For example, `var : VarKind -> Nat -> Term` where `VarKind = Term | Type` encodes the multi-sorted idea using only variable constructor and hence one substitution.

This accomplished by treating substitutions as sequences of "substitution actions":
```lean
inductive Action T where
| su : T -> Action T
| re : Nat -> Action T

Subst T := Nat -> Action T
```
The `su` constructor encodes a genuine replacement for a variable at the right index with a term. The `re` constructor encodes a renaming where a variable constructor's annotated data is preserved and only its index is modified.

This library supports only mediocre macro support. A user must provide a definition of `smap` that properly handles variables and binders. Additionally, one must prove a host of simplification lemmas that communicate how substitutions commute through the structure of a term. Finally, the required type classes `SubstStable` and `SubstCompose` must be defined, but useful tactics are provided to prove these goals automatically.

Because facts about reduction are usually tightly tied ones handling of substitution this library also includes some basic theory of abstract rewriting in `LeanSubst/Reduction.lean` and `LeanSubst/Normal.lean`.

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

Syntax must be non-indexed and single-sorted, see "Examples" for the various requirements needed to properly set up an inductive type encoding syntax.

Other non-trivial uses of this library are available here:
1. [A formalization of the metatheory of STLC](https://github.com/amarmaduke/lean-stlc)