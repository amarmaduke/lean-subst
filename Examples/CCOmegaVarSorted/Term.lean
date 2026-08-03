
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

@[simp, grind =]
theorem Term.from_action_id {n u} : from_action u (𝐬0.act n) = var u n := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_action_succ {n u} : from_action u (𝐬1.act n) = var u (n + 1) := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_acton_re {n u} : from_action u (re n) = var u n := by simp [from_action]

@[simp, grind =]
theorem Term.from_action_su {t u} : from_action u (su t) = t := by simp [from_action]

-- The `coe` stuff doesn't make sense anymore, put we can provide reasonable custom notation
-- Perhaps this should be its own typeclass, dunno
notation:max "↑[" u "]" t => Term.from_action u t

-- instance : Coe (Action Term) Term where
--   coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| var u x => var u (r.act x)
| univ u => univ u
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| lam t1 t2 => lam (t1.rmap r) (t2.rmap $ r.lift)
| pi t1 t2 => pi (t1.rmap r) (t2.rmap $ r.lift)

instance : RenMap Term [Term] where
  rmap r := Term.rmap r.1

@[simp, grind =]
theorem Term.rmap_var {u x} {r : Ren Term} : (var u x)⟨r⟩ = var u (r.act x) := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_univ {u} {r : Ren Term} : (univ u)⟨r⟩ = univ u := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_app {t1 t2} {r : Ren Term} : (app t1 t2)⟨r⟩ = app t1⟨r⟩ t2⟨r⟩ := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_lam {t1 t2} {r : Ren Term} : (lam t1 t2)⟨r⟩ = lam t1⟨r⟩ t2⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp, grind =]
theorem Term.rmap_pi {t1 t2} {r : Ren Term} : (pi t1 t2)⟨r⟩ = pi t1⟨r⟩ t2⟨r.lift⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Term [Term] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term] where
  apply_compose := by sorry

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| var u x => ↑[u] σ.act x
| univ u => univ u
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| lam t1 t2 => lam (t1.smap σ) (t2.smap $ σ.lift)
| pi t1 t2 => pi (t1.smap σ) (t2.smap $ σ.lift)

instance : SubstMap Term [Term] where
  smap σ := Term.smap σ.1

@[simp, grind =]
theorem Term.smap_var {u x} {σ : Subst Term} : (var u x)[σ] = ↑[u] σ.act x := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_univ {u} {σ : Subst Term} : (univ u)[σ] = univ u := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_app {t1 t2 : Term} {σ : Subst Term} : (app t1 t2)[σ] = app t1[σ] t2[σ] := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_lam {t1 t2 : Term} {σ : Subst Term} : (lam t1 t2)[σ] = lam t1[σ] t2[σ.lift] := by
  simp [SubstMap.smap]

@[simp, grind =]
theorem Term.smap_pi {t1 t2 : Term} {σ : Subst Term} : (pi t1 t2)[σ] = pi t1[σ] t2[σ.lift] := by
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

end CCOmegaVarSorted
