-- Theorems that where needed for some development but not yet sorted appropriately

import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class
import LeanSubst.Laws
import LeanSubst.Types.Nat
import LeanSubst.Types.List

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

instance [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T] : SubstMapRenComposeLeft (List S) T where
  apply_ren_compose_left := by intro s r τ; induction s <;> simp [*]

instance [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T] : SubstMapRenComposeRight (List S) T where
  apply_ren_compose_right := by intro s r τ; induction s <;> simp [*]

@[simp, grind =]
theorem Subst.rewrite3_cons_ren_fix [RenMap T T] [SubstMap T T] {a} {σ : Subst T} {r : Ren T}
  : (a :: σ) ∘ r = a⟨r⟩:: (σ ∘ r)
:= by
  simp [cons, compose_ren_right]
  funext; case _ x =>
  cases x; all_goals simp [act, SubstAction.act]

@[simp, grind =]
theorem Subst.rewrite3_cons_ren_subst [SubstMap T T] {x} {σ : Subst T} {r : Ren T}
  : (x :: r) ∘ σ = σ.act x :: (r ∘ σ)
:= by
  simp [cons, compose_ren_left]
  funext; case _ x =>
  cases x; all_goals simp [act, SubstAction.act]

@[simp, grind =]
theorem Subst.ren_succ_beta_to {a} {r : Ren T}
  : (r ∘ Ren.succ T) ∘ (a :: Subst.id T) = r.to
:= by simp [compose_ren_left, Ren.to]

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

@[grind =]
theorem Subst.compose_commute_add [RenMap T T] [SubstMap T T] [SubstMapStable T T] {k} {τ : Subst T}
  : τ ∘ add T k = add T k ∘ τ.lift k
:= by
  simp [compose]; funext; case _ x =>
  generalize zdef : τ.act x = z
  cases z <;> simp
  rw [apply_stable]; simp

@[grind =]
theorem Subst.compose_commute_add_ren_subst [RenMap T T] [SubstMap T T] [SubstMapStable T T] {k} {τ : Subst T}
  : τ ∘ Ren.add T k = Ren.add T k ∘ τ.lift k
:= by
  simp [compose_ren_right, compose_ren_left]

@[grind =]
theorem Subst.compose_commute_add_ren [RenMap T T] {k} {r : Ren T}
  : r ∘ add T k = add T k ∘ r.lift k
:= by
  simp [compose_ren_left, compose_ren_right]

@[grind =]
theorem Subst.compose_commute_add_ren_ren {k} {r : Ren T}
  : r ∘ Ren.add T k = .add T k ∘ r.lift k
:= by simp [Ren.compose]

@[simp]
theorem Ren.to_cons {x} {r : Ren T} : (x::r).to = re x :: r.to := by
  simp [to, cons, Subst.cons]; funext; case _ x =>
  cases x <;> simp

theorem Subst.rewrite1_append_ren_le {T s e} : s..e ++ +r e = .add T (min s e) := by
  induction e generalizing s; simp
  case _ e ih =>
  cases Nat.decLt s (e + 1)
  case _ h1 =>
    have lem : s ≥ e + 1 := by omega
    rw [Ren.range_ge_nil (h := lem)]; simp
    rw [Nat.min_eq_right lem]
  case _ h1 =>
    rw [Ren.range_lt_cons (h := h1)]
    rw [Nat.min_eq_left (by omega)]
    simp
    have lem : (s + 1)..(e + 1) ++ Ren.add T (e + 1) = .succ T ∘ (s..e ++ Ren.add T e) := sorry
    rw [lem, ih, Nat.min_eq_left (by omega)]
    sorry

theorem Subst.rewrite1_append_le {T s e} : s..e ++ +σ e = add T (min s e) := by
  induction e generalizing s; simp
  case _ e ih =>
  cases Nat.decLt s (e + 1)
  case _ h1 =>
    have lem : s ≥ e + 1 := by omega
    rw [Ren.range_ge_nil (h := lem)]; simp
    rw [Nat.min_eq_right lem]
  case _ h1 =>
    rw [Ren.range_lt_cons (h := h1)]
    rw [Nat.min_eq_left (by omega)]
    simp
    have lem : (s + 1)..(e + 1) ++ add T (e + 1) = .succ T ∘ (s..e ++ add T e) := sorry
    rw [lem, ih, Nat.min_eq_left (by omega)]
    sorry

@[simp, grind =]
theorem Subst.rewrite1_append_ren {e} : 0..e ++ +r e = .id T := by
  have lem := @rewrite1_append_ren_le T 0 e
  simp at lem; exact lem

@[simp, grind =]
theorem Subst.rewrite1_append {e} : 0..e ++ +σ e = id T := by
  have lem := @rewrite1_append_le T 0 e
  simp at lem; exact lem

@[simp, grind =]
theorem Subst.rewrite_lift_ren {r : Ren T} : r.lift = 0::(r ∘ +1r) := by
  simp [Ren.lift, Ren.cons]; funext; case _ x =>
  cases x <;> simp

@[simp, grind =]
theorem Subst.rewrite3_append_ren_ren_cons {x} {r1 r2 : Ren T}
  : (x::r1) ∘ r2 = r2.act x::(r1 ∘ r2)
:= by
  simp [Ren.cons, Ren.compose]; funext; case _ x =>
  cases x <;> simp

@[simp, grind =]
theorem Subst.rewrite3_append_ren_ren {ℓ : List Nat} {r1 r2 : Ren T}
  : (ℓ ++ r1) ∘ r2 = ℓ⟨r2⟩ ++ (r1 ∘ r2)
:= by
  induction ℓ generalizing r1 r2 <;> simp [*]

@[simp]
theorem range_act_succ_ren_fixed {s e}
  : (s..e)⟨.succ T⟩ = s.succ..e.succ
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
theorem Subst.rewrite_lift_k_ren {k} {r : Ren T} : r.lift k = 0..k ++ (r ∘ +r k) := by
  induction k generalizing r <;> simp
  case _ k ih =>
  rw [Ren.lift_of_succ, ih]; simp
  rw [<-Ren.compose_add_succ_right]

@[simp, grind =]
theorem Subst.rewrite4_cons_ren_add_direct {r : Ren T} {ℓ : List Nat}
  : Ren.add T ℓ.length ∘ (ℓ ++ r) = r
:= by simp [Ren.compose]

@[simp, grind =]
theorem Subst.rewrite4_cons_ren_add_indirect {k} {r : Ren T} {ℓ : List Nat} {h : k = ℓ.length}
  : Ren.add T k ∘ (ℓ ++ r) = r
:= by simp [Ren.compose, h]

@[simp, grind =]
theorem Subst.rewrite4_append_add_direct {σ : Subst T} {ℓ : List (Action T)}
  : Ren.add T ℓ.length ∘ (ℓ ++ σ) = σ
:= by simp [compose_ren_left]; congr

@[simp, grind =]
theorem Subst.rewrite4_append_add_indirect {k} {σ : Subst T} {ℓ : List (Action T)} {h : k = ℓ.length}
  : Ren.add T k ∘ (ℓ ++ σ) = σ
:= by simp [compose_ren_left, h]; congr

theorem Subst.compose_ren_left_cons_lift_1 [RenMap T T] [SubstMap T T] {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift ∘ (a :: σ) = a :: (r ∘ σ)
:= by
  simp; congr 1

@[simp]
theorem Subst.compose_ren_left_cons_lift_k1 [RenMap T T] [SubstMap T T] {k} {a : Action T} {r : Ren T} {σ : Subst T}
  : r.lift (k + 1) ∘ (a :: σ) = a :: (r.lift k ∘ σ)
:= by
  rw [Ren.lift_of_succ, compose_ren_left_cons_lift_1]

@[simp, grind =]
theorem Subst.compose_ren_left_cons_lift_direct
  [RenMap T T] [SubstMap T T] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
  : r.lift ℓ.length ∘ (ℓ ++ σ) = ℓ ++ (r ∘ σ)
:= by
  induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

@[simp, grind =]
theorem Subst.compose_ren_left_cons_lift_indirect
  [RenMap T T] [SubstMap T T] {k} {ℓ : List $ Action T} {r : Ren T} {σ : Subst T} {h : k = ℓ.length}
  : r.lift k ∘ (ℓ ++ σ) = ℓ ++ (r ∘ σ)
:= by
  induction ℓ generalizing r <;> simp [-Subst.rewrite_lift_k_ren, *]

@[simp, grind =]
theorem Subst.compose_ren_right_append [RenMap T T] {ℓ : List $ Action T} {r : Ren T} {σ : Subst T}
  : (ℓ ++ σ) ∘ r = ℓ⟨r⟩ ++ σ ∘ r
:= by
  induction ℓ generalizing σ r <;> simp
  case _ hd tl ih =>
  rw [<-ih]; simp [compose_ren_right, cons]; funext; case _ i =>
  cases i <;> simp

theorem Subst.compose_ren_right_assoc
  [RenMap S S] [SubstMap S S] [SubstMapRenComposeLeft S S]
  {σ τ : Subst S} {r : Ren S}
  : (σ ∘ r) ∘ τ = σ ∘ (r ∘ τ)
:= by
  simp [compose, compose_ren_left, compose_ren_right]; funext; case _ i =>
  generalize zdef : σ.act i = z
  cases z <;> simp
  congr

theorem Subst.compose_ren_right_assoc2
  [RenMap S S] [SubstMap S S] [SubstMapRenComposeRight S S]
  {σ τ : Subst S} {r : Ren S}
  : (σ ∘ τ) ∘ r = σ ∘ (τ ∘ r)
:= by
  simp [compose, compose_ren_right]; funext; case _ i =>
  generalize zdef : σ.act i = z
  cases z <;> simp
  congr

-- like rewrite_lift_succ but no [RenMapId S S]
theorem Subst.lift_of_succ [RenMap S S] [RenMapCompose S S] {k} {σ : Subst S} : σ.lift (k + 1) = (σ.lift k).lift := by
  simp [lift]
  funext n ; induction n
  case zero => simp
  case succ n' _  =>
    simp
    split <;> simp [rmap]
    split <;> grind [Ren.add, Ren.succ, Ren.compose]

theorem Subst.lift_of_succ_rev [RenMap S S] [RenMapCompose S S] {k} {σ : Subst S} : σ.lift (1 + k) = σ.lift.lift k := by
  rw [Nat.add_comm, lift_of_succ]
  simp [lift]
  funext n ; induction n
  case zero => simp [eq_comm]
  case succ n' _ =>
    repeat any_goals (simp ; split)
    · simp ; omega
    · grind [Ren.succ, Ren.add, Ren.compose]
    · grind
    · split <;>
      · simp [Ren.succ, Ren.add, Ren.compose] ; grind

@[grind =]
theorem Subst.lift_of_add [RenMap S S] [RenMapId S S] [RenMapCompose S S] {a b} {σ : Subst S} : σ.lift (a + b) = (σ.lift a).lift b := by
  induction a generalizing σ <;> grind [lift_of_succ_rev]

@[simp]
theorem Subst.ren_to_hcompose [SubstMap S T] {r : Ren S} {σ : Subst T} : r.to ◾ σ = r.to := by simp [hcompose, Ren.to]

@[simp]
theorem Subst.ren_to_hcompose_ren [RenMap S T] {r : Ren S} {k : Ren T} : r.to ◾ k = r.to := by simp [hcompose_ren, Ren.to]

@[simp]
theorem Subst.to_append {ℓ : List Nat} {r : Ren T} : (ℓ ++ r).to = ℓ ++ r.to := by
  induction ℓ <;> simp_all [HAppend.hAppend, Ren.append, append_ren]

@[simp, grind =]
theorem Subst.ren_rewrite1 [RenMap T T] {r : Ren T} : id T ∘ r = r.to := by simp [Ren.to, compose_ren_right]

@[simp, grind =]
theorem Subst.ren_rewrite1_left {r : Ren T} : r ∘ id T = r.to := by simp [Ren.to, compose_ren_left]

-- Not used but maybe useful
theorem Subst.rmap_of_succ_smap
  [RenMap T T] [SubstMap T T] [RenMapId T T] [SubstMapCompose T T] [SubstMapRenComposeLeft T T]
  {x : Action T} {τ : Subst T} {t : T}
  : t⟨Ren.succ T⟩[x :: τ] = t[τ] := by simp

theorem Subst.compose_compose_left_succ
  [RenMap T T] [SubstMap T T] [RenMapId T T] [SubstMapCompose T T] [SubstMapRenComposeLeft T T]
  {x : Action T} {σ τ : Subst T}
  : (σ ∘ Ren.succ T) ∘ (x :: τ) = σ ∘ τ := by
  simp [compose, smap]
  congr ; funext n
  generalize zdef : σ.act n = z
  induction z <;> simp

theorem Subst.compose_left_cons_lift1_indirect
  [RenMap T T] [SubstMap T T] [RenMapId T T] [SubstMapCompose T T] [SubstMapRenComposeLeft T T]
  {x : Action T} {σ τ : Subst T}
  : σ.lift ∘ (x :: τ) = x :: (σ ∘ τ) := by
  rw [rewrite_lift, rewrite3_cons, Action.smap_re, cons_action0]
  congr 1
  exact compose_compose_left_succ

theorem Subst.compose_left_cons_lift_indirect {k}
  [RenMap T T] [SubstMap T T] [RenMapId T T] [RenMapCompose T T] [SubstMapCompose T T] [SubstMapRenComposeLeft T T]
  {ℓ : List $ Action T} {σ τ : Subst T} {h : k = ℓ.length}
  : σ.lift k ∘ (ℓ ++ τ) = ℓ ++ (σ ∘ τ) := by
  induction ℓ generalizing k <;> simp [*]
  case cons x xs ih => rw [lift_of_succ, compose_left_cons_lift1_indirect, ← @ih xs.length rfl]

theorem Subst.compose_lift_append_indirect {k}
  [RenMap S S] [RenMapId S S] [RenMapCompose S S]
  [SubstMap S S] [SubstMapId S S]
  [SubstMapRenComposeLeft S S] [SubstMapCompose S S]
  {ℓ1 ℓ2 : List (Action S)} (h : k = ℓ2.length)
  : (ℓ1 ++ Subst.id S).lift k ∘ (ℓ2 ++ Subst.id S) = (ℓ2 ++ ℓ1) ++ Subst.id S := by grind [compose_left_cons_lift_indirect]

@[simp]
theorem Subst.List.smap_append [SubstMap S T] {a b : List S} {σ : Subst T}
  : (a ++ b)[σ] = a[σ] ++ b[σ] := by induction a <;> grind

@[simp]
theorem Subst.List.rmap_reverse [RenMap S T] {ℓ : List S} {r : Ren T} : ℓ.reverse⟨r⟩ = ℓ⟨r⟩.reverse := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.smap_reverse [SubstMap S T] {ℓ : List S} {σ : Subst T} : ℓ.reverse[σ] = ℓ[σ].reverse := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.rmap_map_su [RenMap T T] {ℓ : List T} {r : Ren T} : (List.map su ℓ)⟨r⟩ = List.map su ℓ⟨r⟩ := by
  induction ℓ <;> simp ; grind

@[simp]
theorem Subst.List.smap_map_su [SubstMap T T] {ℓ : List T} {σ : Subst T} : (List.map su ℓ)[σ] = List.map su ℓ[σ] := by
  induction ℓ <;> simp ; grind

end LeanSubst
