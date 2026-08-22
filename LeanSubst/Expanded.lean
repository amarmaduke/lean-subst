
import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 T3 : Type u2} {U : Type u3}
variable {V : List (Type u2)}


@[grind =_]
theorem RenVec.get_eta1 {r : RenVec [T1]} : r = (r.get T1 0, .unit) := sorry

@[grind =_]
theorem RenVec.get_eta2 {r : RenVec [T1, T2]} : r = (r.get T1 0, r.get T2 1, .unit) := sorry

@[grind =_]
theorem SubstVec.get_eta1 {σ : SubstVec [T1]} : σ = (σ.get T1 0, .unit) := sorry

@[grind =_]
theorem SubstVec.get_eta2 {σ : SubstVec [T1, T2]} : σ = (σ.get T1 0, σ.get T2 1, .unit) := sorry

@[simp]
theorem RenVec.compose_components1 {r1 k1 : Ren T1}
  : HAndThen.hAndThen (α := RenVec [T1]) (β := RenVec [T1])
    (r1, PUnit.unit) (λ _ => (k1, PUnit.unit))
    = (r1 >> k1, PUnit.unit)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_components2 {r1 k1 : Ren T1} {r2 k2 : Ren T2}
  : HAndThen.hAndThen (α := RenVec [T1, T2]) (β := RenVec [T1, T2])
    (r1, r2, PUnit.unit) (λ _ => (k1, k2, PUnit.unit))
    = (r1 >> k1, r2 >> k2, PUnit.unit)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_components1 {σ1 τ1 : Subst T1} [SubstMapAll [T1]]
  : HAndThen.hAndThen (α := SubstVec [T1]) (β := SubstVec [T1])
    (σ1, PUnit.unit) (λ _ => (τ1, PUnit.unit))
    = (σ1 >> τ1, PUnit.unit)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_components2 {σ1 τ1 : Subst T1} {σ2 τ2 : Subst T2} [SubstMapAll [T1, T2]]
  : HAndThen.hAndThen (α := SubstVec [T1, T2]) (β := SubstVec [T1, T2])
    (σ1, σ2, PUnit.unit) (λ _ => (τ1, τ2, PUnit.unit))
    = (σ1 >> τ1, σ2 >> τ2, PUnit.unit)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

end LeanSubst
