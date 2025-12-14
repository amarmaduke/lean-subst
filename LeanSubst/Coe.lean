import LeanSubst.Basic

open Coe

namespace LeanSubst
  universe u

  namespace Subst
    namespace Action
      @[coe]
      def coe_map {A B} [Coe A B] : Action A -> Action B
      | .re k => .re k
      | .su t => .su t

      instance {A B} [Coe A B] : Coe (Action A) (Action B) where
        coe := coe_map
    end Action

    @[coe]
    def coe_map {A B} [Coe A B] : Subst A -> Subst B
    | σ, n => σ n

    instance {A B} [Coe A B] : Coe (Subst A) (Subst B) where
      coe := coe_map

    class CommutesWithSmap (A B) [SubstMap A] [SubstMap B] [c : Coe A B] where
      coe_commutes : ∀ a (σ : Subst A), coe (a[σ]) = (coe a)[coe (β := Subst B) σ]

    @[simp]
    theorem coe_cons {A B} {a : Subst.Action A} {σ : Subst A} [Coe A B]
      : coe (a :: σ) = (coe a) :: (coe (β := Subst B) σ)
    := by
      funext; case _ x =>
      simp; cases x <;> simp [Coe.coe, coe_map]

    @[simp]
    theorem coe_comp {A B} {σ τ : Subst A}
      [SubstMap A] [SubstMap B] [Coe A B] [i : CommutesWithSmap A B]
      : coe (β := Subst B) (σ ∘ τ) = (coe (β := Subst B) σ) ∘ (coe (β := Subst B) τ)
    := by
      funext; case _ x =>
      simp [Coe.coe, coe_map, Action.coe_map, Subst.compose]
      generalize zdef : σ x = z at *
      cases z <;> simp
      case _ a =>
        rw [CommutesWithSmap.coe_commutes]
        simp [Coe.coe]
  end Subst
end LeanSubst
