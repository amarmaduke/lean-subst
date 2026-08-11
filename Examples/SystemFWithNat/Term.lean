
import LeanSubst
import LeanSubst.Automation.Attributes
import LeanSubst.Automation.Basic

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

#leansubst var Ty.var
#leansubst bind Ty at pos 0 in Ty.all

#eval do
  pure (LeanSubstAttributes.leanSubstBinder.getParam? (← Lean.MonadEnv.getEnv) ``Ty.all)

#leansubst var Term.var
#leansubst bind Term at pos 1 in Term.lam
#leansubst bind Ty at pos 0 in Term.tlam
#leansubst bind 2 of Term at pos 2 in Term.nrec

#leansubst generate Ty, Term

-- Ty --
#print Ty.rmap
#print Ty.rmap._f

#print Ty.rmap_var
#print Ty.rmap_arrow
#print Ty.rmap_all
#print Ty.rmap_nat

#print Ty.smap

-- Term --
#print Term.rmap
#print Term.rmap._f

#print Term.rmap_var
#print Term.rmap_app
#print Term.rmap_lam
#print Term.rmap_tapp
#print Term.rmap_tlam
#print Term.rmap_zero
#print Term.rmap_succ
#print Term.rmap_nrec

#print Term.smap
#print Term.smap._f


----------------------------------------------------------------------------------------------------
-- Ty Renaming & Substitution
----------------------------------------------------------------------------------------------------

-- This is just STLC with some constants

-- instance : RenMap Ty [Ty] where
  -- rmap := sorry

-- instance : SubstMap Ty [Ty] where
  -- smap := sorry

----------------------------------------------------------------------------------------------------
-- Term Renaming & Substitution
----------------------------------------------------------------------------------------------------

-- @[coe]
-- def Term.from_action : Action Term -> Term
-- | re y => var y
-- | su t => t

-- @[simp, grind =]
-- theorem Term.from_action_id {n} : from_action (𝐬0.act n) = var n := by
--   simp [from_action]

-- @[simp, grind =]
-- theorem Term.from_action_succ {n} : from_action (𝐬1.act n) = var (n + 1) := by
--   simp [from_action]

-- @[simp, grind =]
-- theorem Term.from_action_re {n} : from_action (re n) = var n := by simp [from_action]

-- @[simp, grind =]
-- theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

-- instance : Coe (Action Term) Term where
--   coe := Term.from_action

@[simp]
def Term.rmap' (r : RenVec [Term, Ty]) : Term -> Term
| var x => var ((r.get 0).act x)
| app t1 t2 => app (t1.rmap' r) (t2.rmap' r)
| lam A t => lam A⟨r.get 1⟩ (rmap' (r.lift [1, 0]) t)
| tapp t A => tapp (t.rmap' r) A⟨r.get 1⟩
| tlam t => tlam (t.rmap' $ r.lift [0, 1])
| zero => zero
| succ t => succ (t.rmap' r)
| nrec motive z s n => nrec motive⟨r.get 1⟩ (z.rmap' r) (s.rmap' $ r.lift [2, 0]) (n.rmap' r)

theorem rmap_correct : Term.rmap' = Term.rmap := by
  funext r t
  induction t generalizing r
  case var n => simp
  case app t1 t2 ih1 ih2 => simp [ih1, ih2]
  case tapp t' A ih => simp [ih]
  case lam A t' ih => simp [ih]
  case tlam t' ih => simp [ih]
  case zero => simp
  case nrec motive z s n ih1 ih2 ih3 => simp [ih1, ih2, ih3]
  case succ t' ih => simp [ih]

instance : RenMap Term [Term, Ty] where
  rmap := Term.rmap'

theorem Term.rmap_var' {x0} (r : RenVec [Term, Ty]) : (var x0)⟨r,⟩ = var (r.1.act (x0)) := rfl

-- instance : RenMap Term [Term] where
  -- rmap r := Term.rmap ⟨r.1, Ren.id Ty, .unit⟩

-- instance : RenMap Term [Ty] where
  -- rmap r := Term.rmap ⟨Ren.id Term, r.1, .unit⟩

-- instance : SubstMap Ty [Ty] where
  -- smap := sorry

theorem blah : Ren.succ Ty = ⟨fun x ↦ x + 1⟩ := rfl

@[simp]
def Term.smap' (σ : SubstVec [Term, Ty]) : Term -> Term
| var x => (σ.get 0).act x
| app t1 t2 => app (t1.smap' σ) (t2.smap' σ)
| lam A t => lam A[σ.get 1] (t.smap' $ σ.map 𝐭[.lift, id])
| tapp t A => tapp (t.smap' σ) A[σ.get 1]
| tlam t => tlam (t.smap' $ σ.map 𝐭[(·⟨Ren.add Ty 1⟩), .lift])
| zero => zero
| succ t => succ (t.smap' σ)
| nrec motive z s n => nrec motive[σ.get 1] (z.smap' σ) (s.smap' $ σ.map 𝐭[.lift (k := 2), id]) (n.smap' σ)

theorem smap_correct : Term.smap' = Term.smap := by
  funext σ t
  induction t generalizing σ
  case var n => simp
  case app t1 t2 ih1 ih2 => simp [ih1, ih2]
  case tapp t' A ih => simp [ih]
  case lam A t' ih => simp [ih] ; congr
  case tlam t' ih => simp [ih] ; congr
  case zero => simp
  case succ t ih => simp [ih]
  case nrec motive z s n ih1 ih2 ih3 => simp [ih1, ih2, ih3] ; congr

-- @[simp]
-- def Term.smap (σ : Subst Term) (τ : Subst Ty) : Term -> Term
-- | var x => σ.act x
-- | app t1 t2 => app (t1.smap σ τ) (t2.smap σ τ)
-- | lam A t => lam A[τ] (t.smap σ.lift τ)
-- | tapp t A => tapp (t.smap σ τ) A[τ]
-- -- Because `Term` has `Ty` variables, we have to increment `Ty` variables in `σ` by 1
-- --                       v-------v
-- | tlam t => tlam (t.smap σ⟨𝐫1(Ty)⟩ τ.lift)
-- | zero => zero
-- | succ t => succ (t.smap σ τ)
-- | nrec motive z s n => nrec motive[τ] (z.smap σ τ) (s.smap (σ.lift 2) τ) (n.smap σ τ)

end SystemFWithNat
