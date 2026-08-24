
import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

import LeanSubst.Glue

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

@[reducible]
def Subst.typeof {T : Type u2} (_ : T) : Type u2 := T

set_option linter.unusedVariables false in
abbrev Var (T : Type u2) := Nat

structure Ren (T : Type u2) : Type u2 where
  act : Nat -> Nat

@[instance_reducible]
def RenVec : List (Type u2) -> Type u2
| [] => PUnit
| .cons x xs => Ren x × RenVec xs

def RenVec.nil : RenVec [] := PUnit.unit

class RenSuffix (S : Type u1) (V : List (Type u2)) where

class RenMap (S : Type u1) (V : List (Type u2)) where
  rmap : RenVec V -> S -> S

class inductive RenMapAll : List (Type u2) -> Sort _ where
| nil : RenMapAll []
| cons {V Vs} [i1 : RenMap V [V]] [i2 : RenMap V Vs] [i3 : RenSuffix V Vs]
  : RenMapAll Vs -> RenMapAll (V::Vs)

export RenMap (rmap)

macro:max (name := «term_⟨_,⟩») t:term noWs "⟨" r:term ",⟩" : term => `(rmap $r $t)
-- syntax:max (name := «term_⟨_,⟩») term noWs "⟨" term ",⟩" : term
syntax:max (name := «term_⟨_,+⟩») term noWs "⟨" term ,+ "⟩" : term

-- open Lean.Meta in
-- open Lean.Elab.Term in
-- open Subst.Syntax in
-- elab_rules : term
-- | `($t⟨ $r ,⟩) => do
--   let t' <- elabTermAndSynthesize t none
--   let t_ty <- inferType t'
--   let r' <- elabTermAndSynthesize r none
--   let r_ty <- inferType r' |> get_ty_arg
--   let inst_ty : Lean.TSyntax `term <- `(RenMap $(<- exprToSyntax t_ty) $(<- exprToSyntax r_ty))
--   let inst_ty <- elabTermAndSynthesize inst_ty none
--   let (result, _) <- simp inst_ty default
--   let inst <- synthInstance result.expr
--   let stx : Lean.TSyntax `term <- `(@rmap _ _ $(<- exprToSyntax inst) $r $t)
--   elabTermAndSynthesize stx none

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
elab_rules <= expected
| `($t⟨ $elems,* ⟩) => do
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTermAndSynthesize t none :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list elems_ty.reverse
  let elems_stx <- form_prod `(RenVec.nil) elems.reverse
  let stx : TermElabM Lean.Syntax := `(@rmap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTermAndSynthesize stx expected

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

@[instance_reducible]
def SubstVec : List (Type u2) -> Type u2
| [] => PUnit
| .cons x xs => Subst x × SubstVec xs

def SubstVec.nil : SubstVec [] := PUnit.unit

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
| cons {V Vs} [i1 : SubstMap V [V]] [i2 : SubstMap V Vs] [i3 : SubstSuffix V Vs]
  : SubstMapAll Vs -> SubstMapAll (V::Vs)

--  smap : ∀ (i : Fin V.length), SubstMap V[i] [V[i]]

export SubstMap (smap)

macro:max (name := «term_[_,]») t:term noWs "[" σ:term ",]" : term => `(smap $σ $t)
syntax:max (name := «term_[_,+]») term noWs "[" term ,+ "]" : term

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
elab_rules <= expected
| `($t[ $elems,* ]) => do
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTermAndSynthesize t none :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list elems_ty.reverse
  let elems_stx <- form_prod `(SubstVec.nil) elems.reverse
  let stx : TermElabM Lean.Syntax := `(@smap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTermAndSynthesize stx expected

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ ($σ1, SubstVec.nil) $t) => `($t[$σ1])
| `($_ ($σ1, $σ2, SubstVec.nil) $t) => `($t[$σ1, $σ2])
| `($_ ($σ1, $σ2, $σ3, SubstVec.nil) $t) => `($t[$σ1, $σ2, $σ3])
| `($_ $σ $t) => `($t[$σ,])
| _ => throw ()

end LeanSubst
