
import LeanSubst
open LeanSubst

namespace CCOmegaVarSorted

inductive Univ where
| prop
| pred (n : Nat)

inductive Term where
| var : Univ -> Nat -> Term
| univ : Univ -> Term
| app : Term -> Term -> Term
| lam : Term -> Term -> Term
| pi : Term -> Term -> Term

----------------------------------------------------------------------------------------------------
-- Why do we care about annotating variables, or this example in particular?
-- Because it lets us trivially compute the universe of a term:

def Term.universe : Term -> Univ
| var u _ => u
| univ (.prop) => .pred 0
| univ (.pred x) => .pred (x + 1)
| app f _ => f.universe
| lam _ t => t.universe
| pi A B =>
  match A.universe, B.universe with
  | .prop, .prop => .prop
  | .pred u, .prop => .pred (u + 1)
  | .prop, .pred u => .pred (u + 1)
  | .pred u1, .pred u2 => .pred ((max u1 u2) + 1)

-- Without `Univ` annotations on `var` we would need an ambient context
-- (which also means renaming and substitution lemmas..)
-- NOTE: calculation of universes might be off in the `pi` case
----------------------------------------------------------------------------------------------------

-- When we promote `Action Term` to `Term` we need to be given whatever annotation data
@[coe]
def Term.from_action (u : Univ) : Action Term -> Term
| re y => var u y
| su t => t

@[simp]
theorem Term.from_action_id {n u} : from_action u (𝐬0.act n) = var u n := by
  simp [from_action]

@[simp]
theorem Term.from_action_succ {n u} : from_action u (𝐬1.act n) = var u (n + 1) := by
  simp [from_action]

@[simp]
theorem Term.from_acton_re {n u} : from_action u (re n) = var u n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t u} : from_action u (su t) = t := by simp [from_action]

-- The `coe` stuff doesn't make sense anymore, put we can provide reasonable custom notation
-- Perhaps this should be its own typeclass, dunno
notation:max "↑[" u "]" t => Term.from_action u t

@[simp]
def Term.rmap (r : RenVec [Term]) : Term -> Term
| var u x => var u (r.1.act x)
| univ u => univ u
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| lam t1 t2 => lam (t1.rmap r) (t2.rmap $ r.lift [1])
| pi t1 t2 => pi (t1.rmap r) (t2.rmap $ r.lift [1])

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
theorem Term.rmap_var {u x} {r : RenVec [Term]} : (var u x)⟨r,⟩ = var u (r.1.act x) := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_univ {u} {r : RenVec [Term]} : (univ u)⟨r,⟩ = univ u := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_app {t1 t2} {r : RenVec [Term]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_lam {t1 t2} {r : RenVec [Term]} : (lam t1 t2)⟨r,⟩ = lam t1⟨r,⟩ t2⟨r.lift [1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_pi {t1 t2} {r : RenVec [Term]} : (pi t1 t2)⟨r,⟩ = pi t1⟨r,⟩ t2⟨r.lift [1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.from_action_rmap {t : Action Term} {u} {r : RenVec [Term]}
  : (from_action u t)⟨r,⟩ = from_action u t⟨r,⟩
:= by cases t <;> simp

instance : RenMapEmpty Term where
  apply_empty := by intro s; simp

instance : RenMapId Term [Term] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term] where
  apply_compose := by subst_solve_compose

@[simp]
def Term.smap (σ : SubstVec [Term]) : Term -> Term
| var u x => ↑[u] σ.1.act x
| univ u => univ u
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| lam t1 t2 => lam (t1.smap σ) (t2.smap $ σ.lift [1])
| pi t1 t2 => pi (t1.smap σ) (t2.smap $ σ.lift [1])

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
theorem Term.smap_fix {σ : SubstVec [Term]} {t : Term} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Term.smap_var {u x} {σ : SubstVec [Term]} : (var u x)[σ,] = ↑[u] σ.1.act x := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_univ {u} {σ : SubstVec [Term]} : (univ u)[σ,] = univ u := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_app {t1 t2 : Term} {σ : SubstVec [Term]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_lam {t1 t2 : Term} {σ : SubstVec [Term]} : (lam t1 t2)[σ,] = lam t1[σ,] t2[σ.lift [1],] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.smap_pi {t1 t2 : Term} {σ : SubstVec [Term]} : (pi t1 t2)[σ,] = pi t1[σ,] t2[σ.lift [1],] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Term.from_action_smap {t : Action Term} {u} {σ : SubstVec [Term]}
  : (from_action u t)[σ,] = from_action u t[σ,]
:= by cases t <;> simp

instance : SubstMapEmpty Term where
  apply_empty := by intro s; simp

instance : SubstMapId Term [Term] where
  apply_id := by subst_solve_id

instance : SubstMapStable Term [Term] where
  apply_stable := by subst_solve_stable

instance : SubstMapRenComposeLeft Term [Term] where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term [Term] where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Term [Term] where
  apply_compose := by subst_solve_compose

end CCOmegaVarSorted
