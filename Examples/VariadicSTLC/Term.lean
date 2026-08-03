
import LeanSubst
open LeanSubst

namespace VariadicSTLC

inductive Ty where
| base : Ty
| arrow : Ty -> Ty

inductive Term where
| var : Nat -> Term
| app n : Term -> (Fin n -> Term) -> Term
| lam n : (Fin n -> Ty) -> Term -> Term

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
| app n t ts => app n (t.rmap r) (λ i => (ts i).rmap r)
| lam n As t => lam n As (t.rmap $ r.lift n)

instance : RenMap Term [Term] where
  rmap r := Term.rmap r.1

@[simp, grind =]
theorem Term.rmap_var {x} {r : Ren Term} : (var x)⟨r⟩ = .var (r.act x) := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_app {n} {t : Term} {ts  : Fin n -> Term} {r : Ren Term}
  : (app n t ts)⟨r⟩ = app n t⟨r⟩ (λ i => (ts i)⟨r⟩)
:= by simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_lam {n As t} {r : Ren Term} : (lam n As t)⟨r⟩ = lam n As t⟨r.lift n⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Term [Term] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term] where
  apply_compose := by sorry

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| var x => σ.act x
| app n t ts => app n (t.smap σ) (λ i => (ts i).smap σ)
| lam n As t => lam n As (t.smap $ σ.lift n)

instance : SubstMap Term [Term] where
  smap σ := Term.smap σ.1

-- `σ.1.act` might change to `σ[0].act` to prevent things like `σ.2.2.1.act`
@[simp, grind =]
theorem Term.smap_var {x} {σ : SubstVec [Term]} : (var x)[σ,] = from_action (σ.1.act x) := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_app {n} {t : Term} {ts  : Fin n -> Term} {σ : Subst Term}
  : (app n t ts)[σ] = app n t[σ] (λ i => (ts i)[σ])
:= by simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_lam {n As t} {σ : Subst Term} : (lam n As t)[σ] = lam n As t[σ.lift n] := by
  simp [SubstMap.smap]

instance : SubstMapId Term [Term] where
  apply_id := by sorry

instance : SubstMapStable Term [Term] where
  apply_stable := by sorry

instance : SubstMapRenComposeLeft Term [Term] where
  apply_ren_compose_left := by sorry

instance : SubstMapRenComposeRight Term [Term] where
  apply_ren_compose_right := by sorry

instance : SubstMapCompose Term [Term] where
  apply_compose := by sorry

end VariadicSTLC
