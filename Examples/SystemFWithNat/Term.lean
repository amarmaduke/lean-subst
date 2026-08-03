
import LeanSubst
open LeanSubst

namespace SystemFWithNat

inductive Ty where
| var : Nat -> Ty
| arrow : Ty -> Ty -> Ty
| all : Ty -> Ty
| nat : Ty

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam (A : Ty) (t : Term) : Term -- binds Term in t
| tapp : Term -> Ty -> Term
| tlam (t : Term) : Term -- binds Ty in t (does it make sense to allow a user to give a name instead of a position?)
| zero : Term
| succ : Term -> Term
| nrec (motive : Ty) (z : Term) (s : Term) (n : Term) : Term -- binds 2 Term's in s

----------------------------------------------------------------------------------------------------
-- Ty Renaming & Substitution
----------------------------------------------------------------------------------------------------

-- This is just STLC with some constants

instance : RenMap Ty [Ty] where
  rmap := sorry

instance : SubstMap Ty [Ty] where
  smap := sorry

----------------------------------------------------------------------------------------------------
-- Term Renaming & Substitution
----------------------------------------------------------------------------------------------------

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

-- Defining the rmap/smap using the Tuple form might make more sense for a macro, dunno
@[simp]
def Term.rmap (r : RenVec [Term, Ty]) : Term -> Term
| var x => var (r.1.act x)
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| lam A t => lam A⟨r.2.1⟩ (t.rmap $ r.lift [1, 0])
| tapp t A => tapp (t.rmap r) A⟨r.2.1⟩
| tlam t => tlam (t.rmap $ r.lift [0, 1])
| zero => zero
| succ t => succ (t.rmap r)
| nrec motive z s n => nrec motive⟨r.2.1⟩ (z.rmap r) (s.rmap $ r.lift [2, 0]) (n.rmap r)

instance : RenMap Term [Term, Ty] where
  rmap := Term.rmap

instance : RenMap Term [Term] where
  rmap r := Term.rmap (r.1, Ren.id Ty, .unit)

instance : RenMap Term [Ty] where
  rmap r := Term.rmap (Ren.id Term, r.1, .unit)

@[simp]
def Term.smap (σ : Subst Term) (τ : Subst Ty) : Term -> Term
| var x => σ.act x
| app t1 t2 => app (t1.smap σ τ) (t2.smap σ τ)
| lam A t => lam A[τ] (t.smap σ.lift τ)
| tapp t A => tapp (t.smap σ τ) A[τ]
-- Because `Term` has `Ty` variables, we have to increment `Ty` variables in `σ` by 1
--                       v-------v
| tlam t => tlam (t.smap σ⟨𝐫1(Ty)⟩ τ.lift)
| zero => zero
| succ t => succ (t.smap σ τ)
| nrec motive z s n => nrec motive[τ] (z.smap σ τ) (s.smap (σ.lift 2) τ) (n.smap σ τ)


end SystemFWithNat
