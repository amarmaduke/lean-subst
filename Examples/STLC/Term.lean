
import LeanSubst
open LeanSubst

namespace STLC

inductive Ty where
| base : Ty
| arrow : Ty -> Ty

notation "★" => Ty.base
infixr:64 " -:> " => Ty.arrow

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term

prefix:max "#" => Term.var
notation "λ[" A "]" t => Term.lam A t

@[simp]
instance : HSMul Term Term Term where
  hSMul := Term.app

@[coe]
def Term.from_action : Action Term -> Term
| re y => var y
| su t => t

@[simp, grind =]
theorem Term.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_action_succ {n} : from_action (𝐬1.act n) = var (n + 1) := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp, grind =]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| var x => var (r.act x)
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| λ[A] t => λ[A] t.rmap r.lift

instance : RenMap Term [Term] where
  rmap r := Term.rmap r.1

@[simp, grind =]
theorem Term.rmap_var {x} {r : Ren Term} : (#x)⟨r⟩ = .var (r.act x) := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_app {t1 t2 : Term} {r : Ren Term} : (app t1 t2)⟨r⟩ = app t1⟨r⟩ t2⟨r⟩ := by
  simp +instances [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_lam {A t} {r : Ren Term} : (λ[A] t)⟨r⟩ = λ[A] t⟨r.lift⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Term [Term] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term] where
  apply_compose := by sorry

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| var x => σ.act x
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| λ[A] t => λ[A] t.smap σ.lift

instance : SubstMap Term [Term] where
  smap σ := Term.smap σ.1

@[simp, grind =]
theorem Term.smap_var {x} {σ : SubstVec [Term]} : (#x)[σ,] = from_action (σ.1.act x) := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_app {t1 t2 : Term} {σ : SubstVec [Term]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp +instances [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_lam {A t} {σ : SubstVec [Term]} : (λ[A] t)[σ,] = λ[A] t[σ.lift,] := by
  simp [-Subst.rewrite_lift, SubstMap.smap]; sorry

instance : SubstMapId Term [Term] where
  apply_id := by sorry

instance : SubstMapStable Term [Term] where
  apply_stable := by sorry

instance : SubstMapRenComposeLeft Term [Term] where
  apply_ren_compose_left := by sorry

instance : SubstMapRenComposeRight Term [Term] where
  apply_ren_compose_right := by sorry

instance : SubstMapCompose Term [Term] where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    case var => sorry
    case app => simp [*]
    case lam => sorry
    -- any_goals solve | simp_all +instances [List.Tuple]
    -- try any_goals solve | (
    --   try simp_all +instances [List.Tuple]
    --   try simp [-Subst.rewrite_lift, *]
    --   try funext; case _ x =>
    --   try rw [<-Ren.to_lift]
    --   try simp [-Subst.rewrite_lift, *]
    --   try grind)

end STLC
