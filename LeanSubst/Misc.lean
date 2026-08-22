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

instance [RenMap S V] [SubstMap S V] [SubstMapRenComposeLeft S V] : SubstMapRenComposeLeft (List S) V where
  apply_ren_compose_left := by intro s r τ; induction s <;> simp [*]

instance [RenMap S V] [RenMapAll V] [SubstMap S V] [SubstMapRenComposeRight S V] : SubstMapRenComposeRight (List S) V where
  apply_ren_compose_right := by intro s r τ; induction s <;> simp [*]

@[simp]
theorem Subst.rewrite3_cons_ren_fix [RenMap T [T]] [SubstMap T [T]] {a} {σ : Subst T} {r : Ren T}
  : (a :: σ) >> r = a⟨r⟩::(σ >> r)
:= by
  simp [cons, HAndThen.hAndThen, compose_ren_right]
  funext; case _ x =>
  cases x; all_goals simp [act, SubstAction.act]

@[simp]
theorem Subst.rewrite3_cons_ren_subst [SubstMap T [T]] {x} {σ : Subst T} {r : Ren T}
  : (x :: r) >> σ = σ.act x :: (r >> σ)
:= by
  simp [cons, HAndThen.hAndThen, compose_ren_left]
  funext; case _ x =>
  cases x; all_goals simp [act, SubstAction.act]

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

theorem Subst.compose_commute_add [RenMap T [T]] [SubstMap T [T]] [SubstMapStable T [T]] {k} {τ : Subst T}
  : τ >> add T k = add T k >> τ.lift k
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]; funext; case _ x =>
  generalize zdef : τ.act x = z
  cases z <;> simp
  rw [SubstMapStable.apply_stable]; simp [RenVec.to]

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

@[simp]
theorem Ren.to_cons {x} {r : Ren T} : (x::r).to = re x :: r.to := by
  simp [to, cons, Subst.cons]; funext; case _ x =>
  cases x <;> simp

theorem Ren.cons_add_succ {T n} : n :: add T (n + 1) = add T n := by
  induction n
  case zero =>
    simp [cons]
    congr ; funext ; split <;> simp
  case succ =>
    simp [cons, add]
    funext ; split <;> omega

theorem Ren.assoc {T} {xs ys : List Nat} {r : Ren T} : xs ++ (ys ++ r) = xs ++ ys ++ r := by
  induction xs <;> simp_all

theorem Ren.append_range_succ_succ {T s e} {r : Ren T} {h : s ≤ e + 1} : s..(e + 2) ++ r = s..(e + 1) ++ ((e + 1) :: r) := by
  simp_all [Ren.range, ← Ren.assoc]

theorem Subst.rewrite1_append_ren_le {T s e} : s..e ++ Ren.add T e = .add T (min s e) := by
  induction e generalizing s ; simp
  case succ e ih =>
    cases Nat.decLt s (e + 1)
    case isFalse => simp_all
    case isTrue h =>
      cases (by omega : s ≤ e)
      case refl => simp [Ren.cons, Ren.add] ; funext n ; split <;> grind
      case step n _ =>
        replace ih := @ih s
        simp_all [Nat.min_eq_left (by omega : s ≤ n + 2)]
        simp [Nat.min_eq_left (by omega : s ≤ n + 1)] at ih
        rw [← ih, @Ren.append_range_succ_succ (h := (by omega : s + 1 ≤ n + 1)), Ren.cons_add_succ]
        simp [@Ren.range_lt_cons (h := (by omega : s < n + 1))]

theorem subst_append_assoc_nat {T} {xs ys : List Nat} {σ : Subst T} : xs ++ (ys ++ σ) = xs ++ ys ++ σ := by
  induction xs <;> simp_all

theorem Subst.append_range_succ_succ {T s e} {σ : Subst T} {h : s ≤ e + 1} : s..(e + 2) ++ σ = s..(e + 1) ++ ((re $ e + 1) :: σ) := by
  simp_all [Ren.range, subst_append_assoc_nat]

theorem Subst.cons_add_succ {T n} : re n :: add T (n + 1) = add T n := by
  induction n
  case zero =>
    simp [cons]
    congr ; funext n ; split <;> simp
  case succ n _ =>
    simp [cons, add]
    funext ; split <;> congr 1 <;> omega

theorem Subst.rewrite1_append_le {T s e} : s..e ++ add T e = add T (min s e) := by
  induction e generalizing s ; simp
  case succ e ih =>
    cases Nat.decLt s (e + 1)
    case isFalse => simp_all
    case isTrue h1 =>
      cases (by omega : s ≤ e)
      case refl => simp [Subst.cons, Subst.add] ; funext n ; split <;> grind
      case step n _ =>
        replace ih := @ih s
        simp_all [Nat.min_eq_left (by omega : s ≤ n + 2)]
        simp [Nat.min_eq_left (by omega : s ≤ n + 1)] at ih
        rw [← ih, @Subst.append_range_succ_succ (h := (by omega : s + 1 ≤ n + 1)), cons_add_succ]
        simp [@Ren.range_lt_cons (h := (by omega : s < n + 1))]


@[simp, grind =]
theorem Subst.rewrite1_append_ren {e} : 0..e ++ Ren.add T e = .id T := by
  have lem := @rewrite1_append_ren_le T 0 e
  simp at lem; exact lem

@[simp, grind =]
theorem Subst.rewrite1_append {e} : 0..e ++ add T e = id T := by
  have lem := @rewrite1_append_le T 0 e
  simp at lem; exact lem

@[grind =]
theorem Subst.rewrite_lift_ren {r : Ren T} : r.lift = 0::(r >> 𝐫1) := by
  simp [Ren.lift, Ren.cons]; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.rewrite3_append_ren_ren_cons {x} {r1 r2 : Ren T}
  : (x::r1) >> r2 = r2.act x::(r1 >> r2)
:= by
  simp [Ren.cons, HAndThen.hAndThen, AndThen.andThen, Ren.compose]; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.rewrite3_append_ren_ren {ℓ : List Nat} {r1 r2 : Ren T}
  : (ℓ ++ r1) >> r2 = ℓ⟨r2⟩ ++ (r1 >> r2)
:= by
  induction ℓ generalizing r1 r2 <;> simp [*]

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

@[simp, grind =]
theorem Subst.rewrite_lift_k_ren {k} {r : Ren T} : r.lift k = 0..k ++ (r >> Ren.add T k) := by
  induction k generalizing r <;> simp
  case _ k ih =>
  rw [Ren.lift_of_succ, ih]; simp [rewrite_lift_ren]
  rw [<-Ren.compose_add_succ_right]

@[simp]
theorem Subst.rewrite4_cons_ren_add_direct {r : Ren T} {ℓ : List Nat}
  : Ren.add T ℓ.length >> (ℓ ++ r) = r
:= by simp [HAndThen.hAndThen, AndThen.andThen, Ren.compose]

@[simp]
theorem Subst.rewrite4_cons_ren_add_indirect {k} {r : Ren T} {ℓ : List Nat} {h : k = ℓ.length}
  : Ren.add T k >> (ℓ ++ r) = r
:= by simp [HAndThen.hAndThen, AndThen.andThen, Ren.compose, h]

@[simp]
theorem Subst.rewrite4_append_add_direct {σ : Subst T} {ℓ : List (Action T)}
  : Ren.add T ℓ.length >> (ℓ ++ σ) = σ
:= by simp [HAndThen.hAndThen, compose_ren_left]; congr

@[simp]
theorem Subst.rewrite4_append_add_indirect {k} {σ : Subst T} {ℓ : List (Action T)} {h : k = ℓ.length}
  : Ren.add T k >> (ℓ ++ σ) = σ
:= by simp [h]

theorem Subst.compose_ren_left_cons_lift_1 [RenMap T [T]] [SubstMap T [T]] {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift >> (a :: σ) = a :: (r >> σ)
:= by
  simp; congr 1

@[simp]
theorem Subst.compose_ren_left_cons_lift_k1 [RenMap T [T]] [SubstMap T [T]] {k} {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift (k + 1) >> (a :: σ) = a :: (r.lift k >> σ)
:= by
  rw [Ren.lift_of_succ, compose_ren_left_cons_lift_1]

theorem Subst.compose_ren_left_cons_lift_direct
  [RenMap T [T]] [SubstMap T [T]] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
  : r.lift ℓ.length >> (ℓ ++ σ) = ℓ ++ (r >> σ)
:= by
  induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

theorem Subst.compose_ren_left_cons_lift_indirect
  [RenMap T [T]] [SubstMap T [T]] {k} {ℓ : List $ Action T} {r : Ren T} {σ : Subst T} {h : k = ℓ.length}
  : r.lift k >> (ℓ ++ σ) = ℓ ++ (r >> σ)
:= by
  sorry
  --induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

@[simp]
theorem Subst.compose_ren_right_append [RenMap T [T]] [SubstMap T [T]] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
  : (ℓ ++ σ) >> r = ℓ⟨r⟩ ++ (σ >> r)
:= by
  induction ℓ generalizing σ r <;> simp
  case _ hd tl ih => rw [<-ih]

theorem Subst.compose_ren_right_assoc
  [RenMap S [S]] [SubstMap S [S]] [SubstMapRenComposeLeft S [S]]
  {σ τ : Subst S} {r : Ren S}
  : (σ >> r) >> τ = σ >> r >> τ
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, compose_ren_left, compose_ren_right]
  funext; case _ i =>
  generalize zdef : σ.act i = z
  cases z <;> simp
  congr

theorem Subst.compose_ren_right_assoc2
  [RenMap S [S]] [SubstMap S [S]] [SubstMapRenComposeRight S [S]]
  {σ τ : Subst S} {r : Ren S}
  : (σ >> τ) >> r = σ >> τ >> r
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, compose_ren_right]; funext; case _ i =>
  generalize zdef : σ.act i = z
  cases z <;> simp
  congr

-- like rewrite_lift_succ but no [RenMapId S [S]]
theorem Subst.lift_of_succ [RenMap S [S]] [RenMapCompose S [S]] {k} {σ : Subst S} : σ.lift (k + 1) = (σ.lift k).lift := by
  simp [lift]
  funext n ; induction n
  case zero => simp
  case succ n' _  =>
    simp; sorry

theorem Subst.lift_of_succ_rev [RenMap S [S]] [RenMapCompose S [S]] {k} {σ : Subst S} : σ.lift (1 + k) = σ.lift.lift k := by
  sorry
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

@[grind =]
theorem Subst.lift_of_add [RenMap S [S]] [SubstMap S [S]] [RenMapId S [S]]  [RenMapCompose S [S]] {a b} {σ : Subst S} : σ.lift (a + b) = (σ.lift a).lift b := by
  induction a generalizing σ <;> grind [lift_of_succ_rev]

-- @[simp]
-- theorem Subst.ren_to_hcompose [SubstMap S V] {r : Ren S} {σ : Subst T} : r.to ◾ σ = r.to := by simp [hcompose, Ren.to]

-- @[simp]
-- theorem Subst.ren_to_hcompose_ren [RenMap S T] {r : Ren S} {k : Ren T} : r.to ◾ k = r.to := by simp [hcompose_ren, Ren.to]

@[simp]
theorem Subst.to_append {ℓ : List Nat} {r : Ren T} : (ℓ ++ r).to = ℓ ++ r.to := by
  induction ℓ <;> simp_all [HAppend.hAppend, Ren.append, append_ren]

@[simp]
theorem Subst.ren_rewrite1 [RenMap T [T]] {r : Ren T} : id T >> r = r.to := by
  simp [Ren.to, HAndThen.hAndThen, compose_ren_right]

@[simp, grind =]
theorem Subst.ren_rewrite1_left {r : Ren T} : r >> id T = r.to := by
  simp [Ren.to, HAndThen.hAndThen, compose_ren_left]

-- Not used but maybe useful
-- theorem Subst.rmap_of_succ_smap
--   [RenMap T [T]] [RenMapId T [T]]
--   [SubstMap T [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
--   {x : Action T} {τ : Subst T} {t : T}
--   : t⟨Ren.succ T⟩[x :: τ] = t[τ] := by simp [compose_ren_left_tuple]

theorem Subst.compose_compose_left_succ
  [RenMap T [T]] [RenMapId T [T]]
  [SubstMap T [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
  {x : Action T} {σ τ : Subst T}
  : (σ >> Ren.succ T) >> (x :: τ) = σ >> τ := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, compose_ren_right]
  congr ; funext n
  generalize zdef : σ.act n = z
  induction z <;> simp [HAndThen.hAndThen, SubstVec.compose_ren_left, compose_ren_left]; congr

theorem Subst.compose_left_cons_lift1_indirect
  [RenMap T [T]] [RenMapId T [T]]
  [SubstMap T [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
  {x : Action T} {σ τ : Subst T}
  : σ.lift >> (x :: τ) = x :: (σ >> τ) := by
  rw [rewrite_lift, rewrite3_cons]
  congr 1
  exact compose_compose_left_succ

theorem Subst.compose_left_cons_lift_indirect {k}
  [RenMap T [T]] [RenMapId T [T]] [RenMapCompose T [T]]
  [SubstMap T [T]] [SubstMapCompose T [T]] [SubstMapRenComposeLeft T [T]]
  {ℓ : List $ Action T} {σ τ : Subst T} {h : k = ℓ.length}
  : σ.lift k >> (ℓ ++ τ) = ℓ ++ (σ >> τ) := by
  induction ℓ generalizing k <;> simp [*]
  case cons x xs ih => rw [lift_of_succ, compose_left_cons_lift1_indirect, ← @ih xs.length rfl]

theorem Subst.compose_lift_append_indirect {k}
  [RenMap S [S]] [RenMapId S [S]] [RenMapCompose S [S]]
  [SubstMap S [S]] [SubstMapId S [S]] [SubstMapRenComposeLeft S [S]] [SubstMapCompose S [S]]
  {ℓ1 ℓ2 : List (Action S)} (h : k = ℓ2.length)
  : (ℓ1 ++ Subst.id S).lift k >> (ℓ2 ++ Subst.id S) = (ℓ2 ++ ℓ1) ++ Subst.id S
:= by
  sorry
    -- grind [compose_left_cons_lift_indirect]

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

macro "subst_solve_id" : tactic => `(tactic| {
  intro s; induction s
  all_goals
    try solve | simp [*] at *
  -- intro t; induction t
  -- any_goals solve | simp_all +instances
  -- all_goals try simp at *; simp  +instances [*]; grind
})

macro "subst_solve_stable" : tactic => `(tactic| {
  intro r σ h
  funext; case _ t =>
  induction t generalizing r σ
  all_goals
    simp [-Subst.rewrite_lift, -Subst.rewrite_lift_k, -Subst.rewrite_lift_ren, -Subst.rewrite_lift_k_ren, *] at *
    try simp +instances [*]
  all_goals try solve | rw [Subst.apply_stable h]
  all_goals try solve | (rw [<-h]; simp +instances [Ren.to])
  all_goals try repeat funext; grind
})

macro "subst_solve_compose" : tactic => `(tactic| {
  intro s σ τ
  let T := Subst.typeof s
  induction s generalizing σ τ
  all_goals
    try solve | simp; grind
    try solve | simp [*]
    try simp [Subst.lift_compose_ren_right_vec (T := T), *]
    try simp [Subst.rewrite_lift_compose_ren_left_vec (T := T), *]
    try simp [Subst.rewrite_lift_compose_vec (T := T), *]
  -- intro s σ τ
  -- induction s generalizing σ τ
  -- any_goals solve | simp +instances [*]
  -- try any_goals solve | (
  --   try simp [-Subst.rewrite_lift, *]
  --   try funext; case _ x =>
  --   try rw [<-Ren.to_lift]
  --   try simp [-Subst.rewrite_lift, *]
  --   try grind)
})

end LeanSubst
