import LeanSubst.Basic

namespace LeanSubst
  universe u u1 u2

  namespace IdAction

    variable {T : Type u1} [SubstActionVar T] [SubstMap T T]

    @[simp]
    def action_lift : T -> T
    | t => Ren.apply (A := T) (· + 1) t

    @[simp, reducible]
    instance : SubstActionLift T where
      action_lift := action_lift

    @[simp]
    def action_compose : Subst T -> Subst T -> Subst T
    | σ, τ, n => (σ n)[τ]

    @[simp, reducible]
    instance : SubstActionCompose T where
      action_compose := action_compose

    @[simp]
    instance : SubstActionLiftLaws T where
      action_lift_var := by {
        intro n; simp
        sorry
      }

  end IdAction

end LeanSubst
