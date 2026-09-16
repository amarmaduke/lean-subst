
import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

import LeanSubst.Glue

namespace LeanSubst

universe u u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}
variable {V : List (Type u2)}

class AltCons (S : outParam $ Type u1) (T : Type u2) where
  altCons : S -> T -> T

infixr:67 (name := «_.:_») " .: " => AltCons.altCons

@[reducible]
def Subst.typeof {T : Type u2} (_ : T) : Type u2 := T

set_option linter.unusedVariables false in
abbrev Var (T : Type u2) := Nat

structure Ren (T : Type u2) : Type u2 where
  act : Nat -> Nat

inductive RenVec : List (Type u2) -> Type (u2 + 1)
| nil : RenVec []
| cons {T V : _} : Ren T -> RenVec V -> RenVec (T::V)

infixr:67 (name := RenVec.cons_notation) " .: " => RenVec.cons

class RenSuffix (S : Type u1) (V : List (Type u2)) where

class RenMap (S : Type u1) (V : List (Type u2)) where
  rmap : RenVec V -> S -> S

class inductive RenMapAll : List (Type u2) -> Sort _ where
| nil : RenMapAll []
| cons {V Vs} [RenMap V (V::Vs)] : RenMapAll Vs -> RenMapAll (V::Vs)

export RenMap (rmap)

macro:max (name := «term_⟨_,⟩») t:term noWs "⟨" r:term ",⟩" : term => `(rmap $r $t)
syntax:max (name := «term_⟨_,*⟩») term noWs "⟨" term,* "⟩" : term

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
@[term_elab «term_⟨_,*⟩»]
def elab_rmap : TermElab := fun stx expected => do
  let `($t⟨ $elems,* ⟩) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let ren_meta : TermElabM Lean.Syntax := `(Ren _)
  let ren_meta <- ren_meta
  let ren_meta <- elabTerm ren_meta none
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTermAndSynthesize t ren_meta :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list `(List.nil) elems_ty.reverse
  let elems_stx <- form_prod `(RenVec.nil) elems.reverse
  let stx : TermElabM Lean.Syntax := `(@rmap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTermAndSynthesize stx expected

syntax (name := «term·⟨_,*⟩») "·⟨" withoutPosition(term,*,?) "⟩" : term
open Lean in
macro_rules
| `(·⟨ $elems,* ⟩) => do
  let rec expand_renvec_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
    match i, skip with
    | 0,     _     => pure result
    | i + 1, true  => expand_renvec_lit i false result
    | i + 1, false => expand_renvec_lit i true  (<- ``(RenVec.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
  let size := elems.elemsAndSeps.size
  expand_renvec_lit size (size % 2 == 0) (<- ``(RenVec.nil))

@[app_unexpander RenVec.nil]
meta def RenVec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(·⟨⟩)

@[app_unexpander RenVec.cons]
meta def RenVec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(·⟨⟩)      => `(·⟨$x⟩)
  | `(·⟨$xs,*⟩) => `(·⟨$x, $xs,*⟩)
  | _          => throw ()
| _ => throw ()

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ ($r1, RenVec.nil) $t) => `($t⟨$r1⟩)
| `($_ ($r1, $r2, RenVec.nil) $t) => `($t⟨$r1, $r2⟩)
| `($_ ($r1, $r2, $r3, RenVec.nil) $t) => `($t⟨$r1, $r2, $r3⟩)
| `($_ $r $t) => `($t⟨$r,⟩)
| _ => throw ()

inductive Action (T : Type u2) where
| re : Nat -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

structure Subst (T : Type u2) where
  inner : Nat -> Action T

inductive SubstVec : List (Type u2) -> Type (u2 + 1)
| nil : SubstVec []
| cons {T V : _} : Subst T -> SubstVec V -> SubstVec (T::V)

infixr:67 (name := SubstVec.cons_notation) " .: " => SubstVec.cons

class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
  act (σ : Subst T) : A -> U

def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

instance : SubstAction T Nat (Action T) where
  act := Subst.inner

class SubstSuffix (S : Type u1) (V : List (Type u2)) where

class SubstMap (S : Type u1) (V : List (Type u2)) where
  smap : SubstVec V -> S -> S

class inductive SubstMapAll : List (Type u2) -> Sort _ where
| nil : SubstMapAll []
| cons {V Vs} [SubstMap V (V::Vs)] : SubstMapAll Vs -> SubstMapAll (V::Vs)

export SubstMap (smap)

macro:max (name := «term_[_,]») t:term noWs "[" σ:term ",]" : term => `(smap $σ $t)
syntax:max (name := «term_[_,*]») term noWs "[" term ,* "]" : term

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
@[term_elab «term_[_,*]»]
def elab_smap : TermElab := fun stx expected => do
  let `($t[ $elems,* ]) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTermAndSynthesize t none :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list `(List.nil) elems_ty.reverse
  let elems_stx <- form_prod `(SubstVec.nil) elems.reverse
  let stx : TermElabM Lean.Syntax := `(@smap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTermAndSynthesize stx expected

syntax (name := «term·[_,*]») "·[" withoutPosition(term,*,?) "]" : term
open Lean in
macro_rules
| `(·[ $elems,* ]) => do
  let rec expand_substvec_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
    match i, skip with
    | 0,     _     => pure result
    | i + 1, true  => expand_substvec_lit i false result
    | i + 1, false => expand_substvec_lit i true  (<- ``(SubstVec.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
  let size := elems.elemsAndSeps.size
  expand_substvec_lit size (size % 2 == 0) (<- ``(SubstVec.nil))

@[app_unexpander SubstVec.nil]
meta def SubstVec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(·[])

@[app_unexpander SubstVec.cons]
meta def SubstVec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(·[])      => `(·[$x])
  | `(·[$xs,*]) => `(·[$x, $xs,*])
  | _          => throw ()
| _ => throw ()

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ ($σ1, SubstVec.nil) $t) => `($t[$σ1])
| `($_ ($σ1, $σ2, SubstVec.nil) $t) => `($t[$σ1, $σ2])
| `($_ ($σ1, $σ2, $σ3, SubstVec.nil) $t) => `($t[$σ1, $σ2, $σ3])
| `($_ $σ $t) => `($t[$σ,])
| _ => throw ()

end LeanSubst
