
import LeanSubst
open LeanSubst

namespace STLCWithData

variable {V : Type} {B : V -> Nat -> Prop} {C : V -> Nat -> Prop}

inductive Term (V : Type) (B : V -> Nat -> Prop) (C : V -> Nat -> Prop) where
| var : Nat -> Term V B C
| bind {n} (v : V) {h : B v n} (t : Term V B C) (ts : Fin n -> Term V B C) : Term V B C
| ctor {n} (v : V) {h : C v n} (ts : Fin n -> Term V B C) : Term V B C

@[coe]
def Term.from_action : Action (Term V B C) -> (Term V B C)
| re y => var y
| su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (𝐬0.act n) = @var V B C n := by
  simp [from_action]

@[simp]
theorem Term.from_action_succ {n} : from_action (𝐬1.act n) = @var V B C (n + 1) := by
  simp [from_action]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = @var V B C n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t : Term V B C} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action $ Term V B C) (Term V B C) where
  coe := Term.from_action

@[simp]
def Term.rmap (r : RenVec [Term V B C]) : Term V B C -> Term V B C
| var x => var (r.1.act x)
| bind (h := h) v t ts => bind (h := h) v (t.rmap $ r.lift [1]) (λ i => (ts i).rmap r)
| ctor (h := h) v ts => ctor (h := h) v (λ i => (ts i).rmap r)

instance : RenMap (Term V B C) [Term V B C] where
  rmap := Term.rmap

instance : RenSuffix (Term V B C) [] := ⟨⟩
instance : RenMap (Term V B C) [] where
  rmap _ := id

@[simp]
theorem Term.rmap_empty {t : Term V B C} {r : RenVec []} : t⟨r,⟩ = t := by
  simp only [RenMap.rmap, id]

@[reducible, simp]
instance instRenMapAll_Term : RenMapAll [Term V B C] := .cons .nil

@[simp]
theorem Term.rmap_fix {r : RenVec [Term V B C]} {t : Term V B C} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_var {x} {r : RenVec [Term V B C]} : (@var V B C x)⟨r,⟩ = .var (r.1.act x) := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_ctor {n} {v} {h : C v n} {ts : Fin n -> Term V B C} {r : RenVec [Term V B C]} :
  (ctor (h := h) v ts)⟨r,⟩ = ctor (h := h) v (λ i => (ts i)⟨r,⟩)
:= by simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_bind {n} {v} {h : B v n} {t : Term V B C} {ts : Fin n -> Term V B C} {r : RenVec [Term V B C]} :
  (bind (h := h) v t ts)⟨r,⟩ = bind (h := h) v t⟨r.lift [1],⟩ (λ i => (ts i)⟨r,⟩)
:= by simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.from_action_rmap {t : Action $ Term V B C} {r : RenVec [Term V B C]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp

instance : RenMapEmpty $ Term V B C where
  apply_empty := by intro s; simp

instance : RenMapId (Term V B C) [Term V B C] where
  apply_id := by subst_solve_id

instance : RenMapCompose (Term V B C) [Term V B C] where
  apply_compose := by subst_solve_compose

@[simp]
def Term.smap (σ : SubstVec [Term V B C]) : Term V B C -> Term V B C
| var x => σ.1.act x
| bind (h := h) v t ts => bind (h := h) v (t.smap $ σ.lift [1]) (λ i => (ts i).smap σ)
| ctor (h := h) v ts => ctor (h := h) v (λ i => (ts i).smap σ)

instance : SubstMap (Term V B C) [Term V B C] where
  smap := Term.smap

instance : SubstSuffix (Term V B C) [] := ⟨⟩
instance : SubstMap (Term V B C) [] where
  smap _ := id

@[simp]
theorem Term.smap_empty {t : Term V B C} {σ : SubstVec []} : t[σ,] = t := by
  simp only [SubstMap.smap, id]

@[reducible, simp]
instance instSubstMapAll_Ty : SubstMapAll [Term V B C] := .cons .nil

@[simp]
theorem Term.smap_fix {σ : SubstVec [Term V B C]} {t : Term V B C} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Term.smap_var {x} {σ : SubstVec [Term V B C]} : (@var V B C x)[σ,] = σ.1.act x := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_ctor {n} {v} {h : C v n} {ts : Fin n -> Term V B C} {σ : SubstVec [Term V B C]} :
  (ctor (h := h) v ts)[σ,] = ctor (h := h) v (λ i => (ts i)[σ,])
:= by simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_bind {n} {v} {h : B v n} {t : Term V B C} {ts : Fin n -> Term V B C} {σ : SubstVec [Term V B C]} :
  (bind (h := h) v t ts)[σ,] = bind (h := h) v t[σ.lift [1],] (λ i => (ts i)[σ,])
:= by simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.from_action_smap {t : Action (Term V B C)} {σ : SubstVec [Term V B C]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp

instance : SubstMapEmpty (Term V B C) where
  apply_empty := by intro s; simp

instance : SubstMapId (Term V B C) [Term V B C] where
  apply_id := by subst_solve_id

instance : SubstMapStable (Term V B C) [Term V B C] where
  apply_stable := by subst_solve_stable

instance : SubstMapRenComposeLeft (Term V B C) [Term V B C] where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight (Term V B C) [Term V B C] where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose (Term V B C) [Term V B C] where
  apply_compose := by subst_solve_compose

end STLCWithData
