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

@[grind =]
theorem Subst.lift_of_add [RenMap S S] {a b} {σ : Subst S} : σ.lift (a + b) = (σ.lift a).lift b := sorry

@[simp]
theorem Subst.ren_to_hcompose [SubstMap S T] {r : Ren S} {σ : Subst T} : r.to ◾ σ = r.to := sorry

@[simp]
theorem Subst.ren_to_hcompose_ren [RenMap S T] {r : Ren S} {k : Ren T} : r.to ◾ k = r.to := sorry

@[simp]
theorem Subst.to_append {ℓ : List Nat} {r : Ren T} : (ℓ ++ r).to = ℓ ++ r.to := sorry

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
theorem Subst.ren_rewrite1 [RenMap T T] {r : Ren T} : id T ∘ r = r.to := sorry

@[simp, grind =]
theorem Subst.ren_rewrite1_left {r : Ren T} : r ∘ id T = r.to := sorry

theorem Subst.compose_lift_append_indirect {k}
  [RenMap S S] [RenMapId S S] [RenMapCompose S S]
  [SubstMap S S] [SubstMapId S S]
  [SubstMapRenComposeLeft S S] [SubstMapCompose S S]
  {ℓ1 ℓ2 : List (Action S)} (h : k = ℓ2.length)
  : (ℓ1 ++ Subst.id S).lift k ∘ (ℓ2 ++ Subst.id S) = (ℓ2 ++ ℓ1) ++ Subst.id S
:= by
  sorry

theorem Subst.compose_left_cons_lift_indirect {k}
  [RenMap T T] [SubstMap T T] {ℓ : List $ Action T} {σ τ : Subst T} {h : k = ℓ.length}
  : σ.lift k ∘ (ℓ ++ τ) = ℓ ++ (σ ∘ τ)
:= sorry

@[simp]
theorem Subst.List.smap_append [SubstMap S T] {a b : List S} {σ : Subst T}
  : (a ++ b)[σ] = a[σ] ++ b[σ]
:= sorry

@[simp]
theorem Subst.List.rmap_reverse [RenMap S T] {ℓ : List S} {r : Ren T} : ℓ.reverse⟨r⟩ = ℓ⟨r⟩.reverse := sorry

@[simp]
theorem Subst.List.smap_reverse [SubstMap S T] {ℓ : List S} {σ : Subst T} : ℓ.reverse[σ] = ℓ[σ].reverse := sorry

@[simp]
theorem Subst.List.rmap_map_su [RenMap T T] {ℓ : List T} {r : Ren T} : (List.map su ℓ)⟨r⟩ = List.map su ℓ⟨r⟩ := sorry

@[simp]
theorem Subst.List.smap_map_su [SubstMap T T] {ℓ : List T} {σ : Subst T} : (List.map su ℓ)[σ] = List.map su ℓ[σ] := sorry

end LeanSubst
