import LeanSubst.Basic

namespace LeanSubst

  section
    variable {T : Type u} [SubstMap T] [SubstMapStable T]

    omit [SubstMapStable T] in
    theorem lift_rename {σ τ : Subst T} :
      (∀ n k, σ n = .re k -> τ n = .re k) ->
      ∀ n k, σ.lift n = .re k -> τ.lift n = .re k
    := by
      intro h1 n k h2
      cases n
      case _ => exact h2
      case _ n =>
        unfold Subst.lift at *; simp at h2
        generalize ydef : σ n = y at *
        cases y <;> simp at *
        case _ i =>
          rw [h1 n i ydef]; simp [*]

    theorem lift_replace
      {R : T -> T -> Prop}
      (Rs : ∀ {t t' : T} σ, R t t' -> R (t[σ]) (t'[σ]))
      {σ τ : Subst T}
    :
      (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ R t t') ->
      ∀ n t, σ.lift n = .su t -> ∃ t', τ.lift n = .su t' ∧ R t t'
    := by
      intro h1 n t h2
      cases n
      case _ =>
        unfold Subst.lift at *
        simp at *
      case _ n =>
        unfold Subst.lift at *; simp at *
        generalize udef : σ n = u at *
        cases u <;> simp at *
        case _ s =>
          replace h1 := h1 n s udef
          generalize vdef : τ n = v at *
          cases v <;> simp at *
          case _ w =>
            rw [<-h2]
            rw [SubstMapStable.apply_stable (r := (· + 1)) (σ := S)]
            apply Rs S h1
            rw [to_S]
  end

end LeanSubst
