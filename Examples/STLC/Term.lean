
import LeanSubst
open LeanSubst

namespace STLC

inductive Ty where
| base : Ty
| arrow : Ty -> Ty -> Ty

notation "★" => Ty.base
infixr:64 " -:> " => Ty.arrow

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term

prefix:max "#" => Term.var
notation "λ[" A "]" t => Term.lam A t

-- #leansubst var Term.var
-- #leansubst bind Term at pos 1 in Term.lam
-- #leansubst generate Term

@[coe]
def Term.from_action : Action Term -> Term
| re y => var y
| su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp]
theorem Term.from_action_succ {n k} : from_action ((Subst.add _ k).act n) = var (n + k) := by
  simp [from_action]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : RenVec [Term]) : Term -> Term
| var x => var (r.head.act x)
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| λ[A] t => λ[A] t.rmap $ r.lift [1]

-- instance : RenMap Term [Term] where
--   rmap := Term.rmap

@[reducible, simp]
instance instRenMapAll_Term : RenMapAll [Term] := @RenMapAll.cons _ _ ⟨Term.rmap⟩ .nil

@[simp]
theorem Term.rmap_fix {r : RenVec [Term]} {t : Term} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_var {x} {r : RenVec [Term]} : (#x)⟨r,⟩ = .var (r.head.act x) := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_app {t1 t2 : Term} {r : RenVec [Term]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_lam {A t} {r : RenVec [Term]} : (λ[A] t)⟨r,⟩ = λ[A] t⟨r.lift [1],⟩ := by
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
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| λ[A] t => λ[A] t.smap $ σ.lift [1]

-- instance : SubstMap Term [Term] where
--   smap := Term.smap

@[reducible, simp]
instance instSubstMapAll_Ty : SubstMapAll [Term] := @SubstMapAll.cons _ _ ⟨Term.smap⟩ .nil

@[simp]
theorem Term.smap_fix {σ : SubstVec [Term]} {t : Term} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Term.smap_var {x} {σ : SubstVec [Term]} : (#x)[σ,] = from_action (σ.head.act x) := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_app {t1 t2 : Term} {σ : SubstVec [Term]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_lam {A t} {σ : SubstVec [Term]} : (λ[A] t)[σ,] = λ[A] t[σ.lift [1],] := by
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


end STLC
