
import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 T3 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

@[simp, grind =]
theorem RenVec.proj_eta {r : RenVec (T::V)} : (r.1, r.2) = r := by cases r; simp

@[grind =]
theorem RenVec.proj_eta1 {r : RenVec [T1]} : (r.1, .nil) = r := by
  rcases r with ⟨r, u⟩; congr

@[simp, grind =]
theorem SubstVec.proj_eta (σ : SubstVec (T::V)) : (σ.1, σ.2) = σ := by cases σ; simp

@[grind =]
theorem SubstVec.proj_eta1 {σ : SubstVec [T1]} : (σ.1, .nil) = σ := by
  rcases σ with ⟨σ, u⟩; congr

@[simp]
theorem RenVec.lift_size1_0 {r : RenVec [T1]} : r.lift [0] = r := by
  rcases r with ⟨r, rs⟩; simp; congr

@[simp]
theorem SubstVec.lift_size1_0 [RenMapAll [T1]] [RenMapId T1 [T1]] {σ : SubstVec [T1]} : σ.lift [0] = σ := by
  rcases σ with ⟨σ, σs⟩; simp; congr
  unfold Subst.lift; simp; cases σ; simp

-- @[grind =_]
-- theorem RenVec.get_eta1 {r : RenVec [T1]} : r = (r.get T1 0, .nil) := sorry

-- @[grind =_]
-- theorem RenVec.get_eta2 {r : RenVec [T1, T2]} : r = (r.get T1 0, r.get T2 1, .nil) := sorry

-- @[grind =_]
-- theorem SubstVec.get_eta1 {σ : SubstVec [T1]} : σ = (σ.get T1 0, .nil) := sorry

-- @[grind =_]
-- theorem SubstVec.get_eta2 {σ : SubstVec [T1, T2]} : σ = (σ.get T1 0, σ.get T2 1, .nil) := sorry

@[simp]
theorem RenVec.compose_components1 {r1 k1 : Ren T1}
  : HAndThen.hAndThen (α := RenVec [T1]) (β := RenVec [T1])
    (r1, .nil) (λ _ => (k1, .nil))
    = (r1 >> k1, .nil)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_components2 {r1 k1 : Ren T1} {r2 k2 : Ren T2}
  : HAndThen.hAndThen (α := RenVec [T1, T2]) (β := RenVec [T1, T2])
    (r1, r2, .nil) (λ _ => (k1, k2, .nil))
    = (r1 >> k1, r2 >> k2, .nil)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_ren_left_proj {r1 : Ren T} {r2 : RenVec V} {τ1 : Subst T} {τ2 : SubstVec V}
  : HAndThen.hAndThen (α := RenVec (T::V)) (β := SubstVec (T::V))
    (r1, r2) (λ _ => (τ1, τ2))
    = (r1 >> τ1, r2 >> τ2)
:= by sorry

@[simp]
theorem SubstVec.compose_ren_right_proj [RenMapAll (T::V)] {σ1 : Subst T} {σ2 : SubstVec V} {r1 : Ren T} {r2 : RenVec V}
  : HAndThen.hAndThen (α := SubstVec (T::V)) (β := RenVec (T::V))
    (σ1, σ2) (λ _ => (r1, r2))
    = (σ1 >> r1, σ2 >> r2)
:= by sorry

@[simp]
theorem SubstVec.compose_proj [SubstMapAll (T::V)] {σ1 τ1 : Subst T} {σ2 τ2 : SubstVec V}
  : HAndThen.hAndThen (α := SubstVec (T::V)) (β := SubstVec (T::V))
    (σ1, σ2) (λ _ => (τ1, τ2))
    = (σ1 >> τ1, σ2 >> τ2)
:= by sorry

-- @[simp]
-- theorem SubstVec.compose_components1 {σ1 τ1 : Subst T1} [SubstMapAll [T1]]
--   : HAndThen.hAndThen (α := SubstVec [T1]) (β := SubstVec [T1])
--     (σ1, PUnit.unit) (λ _ => (τ1, PUnit.unit))
--     = (σ1 >> τ1, PUnit.unit)
-- := by sorry

-- @[simp]
-- theorem SubstVec.compose_components2 {σ1 τ1 : Subst T1} {σ2 τ2 : Subst T2} [SubstMapAll [T1, T2]]
--   : HAndThen.hAndThen (α := SubstVec [T1, T2]) (β := SubstVec [T1, T2])
--     (σ1, σ2, PUnit.unit) (λ _ => (τ1, τ2, PUnit.unit))
--     = (σ1 >> τ1, σ2 >> τ2, PUnit.unit)
-- := by sorry

end LeanSubst
