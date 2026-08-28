
import Lean.Elab.Term

universe u u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

namespace LeanSubst.Subst.Syntax
  open Lean.Elab.Term

  open Lean in
  def MetaM.promote {α} (x : Meta.MetaM α) : Elab.Term.TermElabM α := x

  def form_list : List Lean.Expr -> TermElabM (Lean.TSyntax `term)
  | [] => `(List.nil)
  | .cons x xs => do
    let xs' <- form_list xs
    `(List.cons $(<- exprToSyntax x) $xs')

  def form_prod (b : TermElabM $ Lean.TSyntax `term)
    : List Lean.Expr -> TermElabM (Lean.TSyntax `term)
  | [] => b
  | .cons x xs => do
    let xs' <- form_prod b xs
    `(Prod.mk $(<- exprToSyntax x) $xs')

  def get_ty_arg (e : TermElabM Lean.Expr) : TermElabM Lean.Expr := do
    let e <- e
    match e with
    | .app _ ty => pure ty
    | _ => Lean.Elab.throwUnsupportedSyntax
end LeanSubst.Subst.Syntax

-- @[instance_reducible]
-- def List.drop' {α : Type u} : (n : Nat) → (xs : List α) → List α
-- | 0, as => as
-- | _ + 1, [] => []
-- | n + 1, _::as => drop' n as

-- @[simp, grind =]
-- theorem List.drop'_nil {α i} : ([] : List α).drop' i = [] := by cases i <;> rfl

-- @[simp, grind =]
-- theorem List.drop'_zero {α} {l : List α} : l.drop' 0 = l := rfl

-- @[simp, grind =]
-- theorem List.drop'_succ_cons {α} {a : α} {l : List α} {i : Nat}
--   : (a :: l).drop' (i + 1) = l.drop' i
-- := rfl
