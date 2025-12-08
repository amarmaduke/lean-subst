import LeanSubst.Basic

namespace LeanSubst
  universe u

  namespace Subst
    namespace Action
      @[simp, coe]
      def coe_map {A B} [Coe A B] : Action A -> Action B
      | .re k => .re k
      | .su t => .su t

      @[simp]
      instance {A B} [Coe A B] : Coe (Action A) (Action B) where
        coe := coe_map
    end Action

    @[simp, coe]
    def coe_map {A B} [Coe A B] : Subst A -> Subst B
    | σ, n => σ n

    @[simp]
    instance {A B} [Coe A B] : Coe (Subst A) (Subst B) where
      coe := coe_map
  end Subst
end LeanSubst
