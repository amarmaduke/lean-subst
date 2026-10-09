
import LeanSubst
open LeanSubst

namespace VariadicSTLC

inductive Ty where
| base : Ty
| arrow : Ty -> Ty

@[reducible]
def Variadic (n : Nat) (ty : Type) := Fin n → ty

inductive Term where
| var : Nat -> Term
| app n : Term -> Variadic n Term -> Term
| lam n : Variadic n Ty -> Term -> Term

@[coe]
def Term.from_action : Action Term -> Term
| re y => var y
| su t => t

@[simp, grind =]
theorem Term.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_action_succ {n k} : from_action ((Subst.add _ k).act n) = var (n + k) := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp, grind =]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : RenVec [Term]) : Term -> Term
| var x => var (r.head.act x)
| app n t ts => app n (t.rmap r) (λ i => (ts i).rmap r)
| lam n As t => lam n As (t.rmap $ r.lift [n])

instance : RenMap Term [Term] where
  rmap r := Term.rmap r

instance : RenSuffix Term [] := ⟨⟩
instance : RenMap Term [] where
  rmap _ := id

@[simp]
theorem Term.rmap_empty {t : Term} {r : RenVec []} : t⟨r,⟩ = t := by
  simp only [RenMap.rmap, id]

@[reducible, simp]
instance instRenMapAll_Term : RenMapAll [Term] := .cons .nil

@[simp]
theorem Term.rmap_fix {r : RenVec [Term]} {t : Term} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_var {x} {r : RenVec [Term]} : (var x)⟨r,⟩ = .var (r.head.act x) := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_app {n} {t : Term} {ts  : Fin n -> Term} {r : RenVec [Term]}
  : (app n t ts)⟨r,⟩ = app n t⟨r,⟩ (λ i => (ts i)⟨r,⟩)
:= by simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_lam {n As t} {r : RenVec [Term]} : (lam n As t)⟨r,⟩ = lam n As t⟨r.lift [n],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.from_action_rmap {t : Action Term} {r : RenVec [Term]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp

instance : RenMapId Term [Term] where
  id_law := by subst_solve_id

instance : RenMapComp Term [Term] where
  compose_law := by subst_solve_compose

@[simp]
def Term.smap (σ : SubstVec [Term]) : Term -> Term
| var x => σ.head.act x
| app n t ts => app n (t.smap σ) (λ i => (ts i).smap σ)
| lam n As t => lam n As (t.smap $ σ.lift [n])

instance : SubstMap Term [Term] where
  smap σ := Term.smap σ

instance : SubstSuffix Term [] := ⟨⟩
instance : SubstMap Term [] where
  smap _ := id

@[simp]
theorem Term.smap_empty {t : Term} {σ : SubstVec []} : t[σ,] = t := by
  simp only [SubstMap.smap, id]

@[reducible, simp]
instance instSubstMapAll_Ty : SubstMapAll [Term] := .cons .nil

@[simp]
theorem Term.smap_var {x} {σ : SubstVec [Term]} : (var x)[σ,] = from_action (σ.head.act x) := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_app {n} {t : Term} {ts  : Fin n -> Term} {σ : SubstVec [Term]}
  : (app n t ts)[σ,] = app n t[σ,] (λ i => (ts i)[σ,])
:= by simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_lam {n As t} {σ : SubstVec [Term]} : (lam n As t)[σ,] = lam n As t[σ.lift [n],] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.from_action_smap {t : Action Term} {σ : SubstVec [Term]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp

instance : SubstMapId Term [Term] where
  id_law := by subst_solve_id

instance : SubstMapStable Term [Term] where
  stable := by sorry --subst_solve_stable

instance : SubstMapRenCompLeft Term [Term] where
  compose_left_law := by subst_solve_compose

instance : SubstMapRenCompRight Term [Term] where
  compose_right_law := by subst_solve_compose

instance : SubstMapComp Term [Term] where
  compose_law := by subst_solve_compose

end VariadicSTLC
