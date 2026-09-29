-- Theorems that where needed for some development but not yet sorted appropriately

import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class
import LeanSubst.Laws
import LeanSubst.Types.Nat
import LeanSubst.Types.List

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

@[simp]
theorem Subst.ren_succ_beta_to {a} {r : Ren T}
  : (r >> Ren.succ T) >> (a :: Subst.id T) = r.to
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose_ren_left, Ren.compose, Ren.to]

theorem Ren.lift_of_succ_rev {k} {r : Ren S} : r.lift (1 + k) = r.lift.lift k := by
  induction k; simp
  case _ k ih =>
  rw [Ren.lift_of_succ, <-ih, <-Ren.lift_of_succ]
  congr 1

@[grind =]
theorem Ren.lift_of_add {a b} {r : Ren S} : r.lift (a + b) = (r.lift a).lift b := by
  induction a generalizing b; simp
  case _ a ih =>
  rw [Ren.lift_of_succ]
  rw [<-Ren.lift_of_succ_rev]
  rw [<-ih]; congr 1; omega

-- theorem Subst.compose_commute_add [RenMap T [T]] [SubstMap T [T]] [SubstMapStable T [T]] {k} {τ : Subst T}
--   : τ >> add T k = add T k >> τ.lift k
-- := by
--   simp [HAndThen.hAndThen, AndThen.andThen, compose]; funext; case _ x =>
--   generalize zdef : τ.act x = z
--   cases z

theorem Subst.compose_commute_add_ren_subst [RenMap T [T]] [SubstMap T [T]] [SubstMapStable T [T]] {k} {τ : Subst T}
  : τ >> Ren.add T k = Ren.add T k >> τ.lift k
:= by
  simp [HAndThen.hAndThen, compose_ren_right, compose_ren_left]

theorem Subst.compose_commute_add_ren [RenMap T [T]] {k} {r : Ren T}
  : r >> add T k = add T k >> r.lift k
:= by
  simp [HAndThen.hAndThen, compose_ren_left, compose_ren_right]

theorem Subst.compose_commute_add_ren_ren {k} {r : Ren T}
  : r >> Ren.add T k = .add T k >> r.lift k
:= by simp [HAndThen.hAndThen, AndThen.andThen, Ren.compose]

theorem Ren.assoc {T} {xs ys : List Nat} {r : Ren T} : xs ++ (ys ++ r) = xs ++ ys ++ r := by
  induction xs <;> simp_all

theorem Ren.append_range_succ_succ {T s e} {r : Ren T} {h : s ≤ e + 1} : s..(e + 2) ++ r = s..(e + 1) ++ ((e + 1) :: r) := by
  simp_all [Ren.range, ← Ren.assoc]


theorem subst_append_assoc_nat {T} {xs ys : List Nat} {σ : Subst T} : xs ++ (ys ++ σ) = xs ++ ys ++ σ := by
  induction xs <;> simp_all

theorem Subst.append_range_succ_succ {T s e} {σ : Subst T} {h : s ≤ e + 1} : s..(e + 2) ++ σ = s..(e + 1) ++ ((re $ e + 1) :: σ) := by
  simp_all [Ren.range, subst_append_assoc_nat]

@[simp]
theorem range_act_succ_ren_fixed {s e}
  : (s..e)⟨Ren.succ T⟩ = s.succ..e.succ
:= by
  induction e generalizing s; simp
  case _ e ih =>
    simp [Ren.range]; split <;> simp
    case _ h =>
    rw [ih]
    cases Nat.decLe (s + 1) e <;> simp [ite]
    case _ h2 =>
      rw [Ren.range_ge_nil]; omega
    case _ h2 =>
      conv =>
        lhs; simp [Ren.range]
      split <;> simp


theorem Subst.compose_ren_left_cons_lift_1 [RenMap T [T]] [SubstMap T [T]] {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift >> (a :: σ) = a :: (r >> σ)
:= by
  simp [Ren.lift, HAndThen.hAndThen, compose_ren_left, cons]
  funext; case _ i =>
  cases i <;> simp

@[simp]
theorem Subst.compose_ren_left_cons_lift_k1 [RenMap T [T]] [SubstMap T [T]] {k} {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift (k + 1) >> (a :: σ) = a :: (r.lift k >> σ)
:= by
  rw [Ren.lift_of_succ, compose_ren_left_cons_lift_1]

theorem Subst.compose_ren_left_cons_lift_direct
  [RenMap T [T]] [SubstMap T [T]] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
  : r.lift ℓ.length >> (ℓ ++ σ) = ℓ ++ (r >> σ)
:= by
  induction ℓ generalizing r <;> simp [*]

-- theorem Subst.compose_ren_left_cons_lift_indirect
--   [RenMap T [T]] [SubstMap T [T]] {k} {ℓ : List $ Action T} {r : Ren T} {σ : Subst T} {h : k = ℓ.length}
--   : r.lift k >> (ℓ ++ σ) = ℓ ++ (r >> σ)
-- := by
--   sorry
  --induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]


-- like rewrite_lift_succ but no [RenMapId S [S]]
-- theorem Subst.lift_of_succ [RenMap S [S]] [RenMapCompose S [S]] {k} {σ : Subst S} : σ.lift (k + 1) = (σ.lift k).lift := by
--   simp [lift]
--   funext n ; induction n
--   case zero => simp
--   case succ n' _  =>
--     simp; sorry

-- theorem Subst.lift_of_succ_rev [RenMap S [S]] [RenMapCompose S [S]] {k} {σ : Subst S} : σ.lift (1 + k) = σ.lift.lift k := by
--   sorry
  -- rw [Nat.add_comm, lift_of_succ]
  -- simp [lift]
  -- funext n ; induction n
  -- case zero => simp [eq_comm]
  -- case succ n' _ =>
  --   repeat any_goals (simp ; split)
  --   · simp ; omega
  --   · grind [Ren.succ, Ren.add, Ren.compose]
  --   · grind
  --   · split <;>
  --     · simp [Ren.succ, Ren.add, Ren.compose_tuple, Ren.compose] ; grind

-- @[grind =]
-- theorem Subst.lift_of_add [RenMap S [S]] [SubstMap S [S]] [RenMapId S [S]]  [RenMapCompose S [S]] {a b} {σ : Subst S} : σ.lift (a + b) = (σ.lift a).lift b := by
--   sorry
  --induction a generalizing σ <;> grind [lift_of_succ_rev]

@[simp]
theorem Subst.compose_ren_right_from_to
  [SubstMap T [T]] [RenMap T [T]] [SubstMapStable T [T]]
  {σ : Subst T} {r : Ren T} :
  σ >> r.to = σ >> r
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, compose_ren_right]
  funext; case _ i =>
  simp [Subst.act, SubstAction.act]
  cases σ; case _ f =>
  simp [SubstMap.smap, RenMap.rmap, smap0, rmap0]
  cases (f i) <;> simp
  rw [SubstMapStable.apply_stable]; simp [RenVec.to]

@[simp]
theorem Subst.compose_compose_left_succ
  [RenMap T [T]] [RenMapId T [T]]
  [SubstMapAll [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
  {x : Action T} {σ τ : Subst T}
  : (σ >> Ren.succ T) >> (x :: τ) = σ >> τ
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, compose_ren_right]; congr

theorem Subst.compose_left_cons_lift1_indirect
  [RenMap T [T]] [RenMapId T [T]]
  [SubstMapAll [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
  {x : Action T} {σ τ : Subst T}
  : σ.lift >> (x :: τ) = x :: (σ >> τ) := by
  rw [rewrite_lift, rewrite3_cons]
  congr 1
  exact compose_compose_left_succ

-- theorem Subst.compose_left_cons_lift_indirect {k}
--   [RenMap T [T]] [RenMapId T [T]] [RenMapCompose T [T]]
--   [SubstMapAll [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
--   {ℓ : List $ Action T} {σ τ : Subst T} {h : k = ℓ.length}
--   : σ.lift k >> (ℓ ++ τ) = ℓ ++ (σ >> τ) := by
--   induction ℓ generalizing k <;> simp [*]
--   case cons x xs ih => rw [lift_of_succ, compose_left_cons_lift1_indirect, ← @ih xs.length rfl]

-- theorem Subst.compose_lift_append_indirect {k}
--   [RenMap S [S]] [RenMapId S [S]] [RenMapCompose S [S]]
--   [SubstMapAll [S]] [SubstMapId S [S]] [SubstMapRenComposeLeft S [S]] [SubstMapCompose S [S]]
--   {ℓ1 ℓ2 : List (Action S)} (h : k = ℓ2.length)
--   : (ℓ1 ++ Subst.id S).lift k >> (ℓ2 ++ Subst.id S) = (ℓ2 ++ ℓ1) ++ Subst.id S
-- := by
--   sorry
--     -- grind [compose_left_cons_lift_indirect]

@[simp]
theorem Subst.List.smap_append [SubstMap S V] {a b : List S} {σ : SubstVec V}
  : (a ++ b)[σ,] = a[σ,] ++ b[σ,] := by induction a <;> grind

@[simp]
theorem Subst.List.rmap_reverse [RenMap S V] {ℓ : List S} {r : RenVec V} : ℓ.reverse⟨r,⟩ = ℓ⟨r,⟩.reverse := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.smap_reverse [SubstMap S V] {ℓ : List S} {σ : SubstVec V} : ℓ.reverse[σ,] = ℓ[σ,].reverse := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.rmap_map_su [RenMap T [T]] {ℓ : List T} {r : Ren T} : (List.map su ℓ)⟨r⟩ = List.map su ℓ⟨r⟩ := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.smap_map_su [SubstMap T [T]] {ℓ : List T} {σ : Subst T} : (List.map su ℓ)[σ] = List.map su ℓ[σ] := by
  induction ℓ <;> simp ; grind

end LeanSubst
