
import Lean.Elab.Term
import Lilac
open Lilac

namespace LeanSubst

universe u

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}
variable {V : List (Type u1)}

namespace Subst.Syntax
  open Lean.Elab.Term

  open Lean in
  def MetaM.promote {α} (x : Meta.MetaM α) : Elab.Term.TermElabM α := x

  def form_list : List Lean.Expr -> TermElabM (Lean.TSyntax `term)
  | [] => `(List.nil)
  | .cons x xs => do
    let xs' <- form_list xs
    `(List.cons $(<- exprToSyntax x) $xs')

  def form_prod : List Lean.Expr -> TermElabM (Lean.TSyntax `term)
  | [] => `(ULift.up Unit.unit)
  | .cons x xs => do
    let xs' <- form_prod xs
    `(Prod.mk $(<- exprToSyntax x) $xs')

  def get_ty_arg (e : TermElabM Lean.Expr) : TermElabM Lean.Expr := do
    let e <- e
    match e with
    | .app _ ty => pure ty
    | _ => Lean.Elab.throwUnsupportedSyntax
end Subst.Syntax

set_option linter.unusedVariables false in
abbrev Var (T : Type u2) := Nat

structure Ren (T : Type u2) where
  act : Var T -> Var T

@[simp]
def List.Tuple (F : Type u1 -> Type u2) : List (Type u1) -> Type u2
| [] => ULift Unit
| .cons x xs => F x × List.Tuple F xs

class RenMap (S : Type u) (V : List (Type u)) where
  rmap : List.Tuple Ren V -> S -> S

export RenMap (rmap)

macro:max (name := «term_⟨_,⟩») t:term noWs "⟨" r:term ",⟩" : term => `(rmap $r $t)
syntax:max (name := «term_⟨_,+⟩») term noWs "⟨" term ,+ "⟩" : term

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
elab_rules <= expected
| `($t⟨ $elems,* ⟩) => do
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTerm t none :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list elems_ty.reverse
  let elems_stx <- form_prod elems.reverse
  let stx : TermElabM Lean.Syntax := `(@rmap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTerm stx expected

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ ($r1, $r2, {down := ()}) $t) => `($t⟨$r1, $r2⟩)
| `($_ ($r1, $r2, $r3, {down := ()}) $t) => `($t⟨$r1, $r2, $r3⟩)
| `($_ $r $t) => `($t⟨$r,⟩)
| _ => throw ()

inductive Action (T : Type u2) where
| re : Var T -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

structure Subst (T : Type u2) where
  inner : Var T -> Action T

class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
  act (σ : Subst T) : A -> U

def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

instance : SubstAction T Nat (Action T) where
  act := Subst.inner

class SubstMap (S : Type u2) (V : List (Type u2)) where
  smap : List.Tuple Subst V -> S -> S

export SubstMap (smap)

macro:max (name := «term_[_,]») t:term noWs "[" σ:term ",]" : term => `(smap $σ $t)
syntax:max (name := «term_[_,+]») term noWs "[" term ,+ "]" : term

open Lean.Meta in
open Lean.Elab.Term in
open Subst.Syntax in
elab_rules <= expected
| `($t[ $elems,* ]) => do
  let elems <- List.mapM id $ elems.getElems.foldl (λ acc t => elabTerm t none :: acc) []
  let elems_ty <- List.mapM id $ elems.map inferType |> List.map MetaM.promote |> List.map get_ty_arg
  let list_ann <- form_list elems_ty.reverse
  let elems_stx <- form_prod elems.reverse
  let stx : TermElabM Lean.Syntax := `(@smap _ $list_ann _ $elems_stx $t)
  let stx <- stx
  elabTerm stx expected

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ ($σ1, $σ2, {down := ()}) $t) => `($t[$σ1, $σ2])
| `($_ ($σ1, $σ2, $σ3, {down := ()}) $t) => `($t[$σ1, $σ2, $σ3])
| `($_ $σ $t) => `($t[$σ,])
| _ => throw ()


def test1 : Subst Nat × ULift Unit -> Nat -> Nat := sorry

instance : SubstMap Nat [Nat] where
  smap := test1

def test2 : Subst Nat × Subst Bool × ULift Unit -> Nat -> Nat := sorry

instance : SubstMap Nat [Nat, Bool] where
  smap := test2

theorem test3 {r1 : Subst Nat} {r2 : Subst Bool} {x : Nat} : x[r1, r2] = x := sorry

theorem test4 [SubstMap S V] {v : List.Tuple Subst V} {x : S} : x[v,] = x := sorry


end LeanSubst
