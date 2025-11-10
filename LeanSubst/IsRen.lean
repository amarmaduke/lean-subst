import LeanSubst.Basic

namespace LeanSubst
  universe u

  class HasSimpleVar (T : Type u) [SubstMap T] where
    var : Nat -> T
    smap {lf f i} : SubstMap.smap lf f (var i) = match (f i) with | .re k => var k | .su t => t

  macro "solve_simple_var_smap" : tactic => `(tactic| {
    intro lf f i; simp [SubstMap.smap]
    try (
      generalize zdef : f i = z at *
      cases z <;> simp)
  })

  namespace HasSimpleVar
    section
      variable {T : Type u} [SubstMap T] [HasSimpleVar T]

      @[simp]
      theorem smap_eq {lf f i} :
        SubstMap.smap lf f (HasSimpleVar.var (T := T) i)
        = match (f i) with | .re k => HasSimpleVar.var k | .su t => t
      := by rw [HasSimpleVar.smap]

      @[simp]
      theorem ren {k} (r : Ren) : Ren.apply r (HasSimpleVar.var k) = HasSimpleVar.var (T := T) (r k) := by
        unfold Ren.apply; simp [Ren.to]

      @[simp]
      theorem sub {i} (σ : Subst T) :
        (HasSimpleVar.var i)[σ] = match (σ i) with | .re k => HasSimpleVar.var k | .su t => t
      := by
        unfold Subst.apply; simp

      theorem re {i k} {σ : Subst T} : σ i = .re k -> (HasSimpleVar.var i)[σ] = HasSimpleVar.var k := by
        intro h; simp [*]

      theorem su {i t} {σ : Subst T} : σ i = .su t -> (HasSimpleVar.var i)[σ] = t := by
        intro h; simp [*]
    end
  end HasSimpleVar

  def IsRen {T : Type u} [SubstMap T] [HasSimpleVar T] (σ : Subst T) : Prop :=
    ∀ i, ∃ k, σ i = .re k ∨ σ i = .su (HasSimpleVar.var k)

  namespace IsRen
    section
      variable {T : Type u} [SubstMap T] [HasSimpleVar T]

      theorem var_forced {i t} {σ : Subst T} :
        IsRen σ ->
        σ i = .su t ->
        ∃ k, t = HasSimpleVar.var k
      := by
        intro h1 h2
        unfold IsRen at h1
        replace h1 := h1 i
        cases h1; case _ k h1 =>
          rw [h2] at h1; simp at h1
          exists k

      theorem var_apply_forced {σ : Subst T} x :
        IsRen σ ->
        ∃ k, (HasSimpleVar.var x)[σ] = HasSimpleVar.var k
      := by
        intro h; unfold IsRen at h
        replace h := h x
        cases h; case _ i h =>
        cases h <;> simp [*]
        case _ h => exists i
        case _ h => exists i

      theorem I : IsRen (T := T) I := by
        unfold IsRen; intro i
        exists i; simp

      theorem S : IsRen (T := T) S := by
        unfold IsRen; intro i
        exists (i + 1); simp

      theorem to (r : Ren) : IsRen (T := T) (r.to) := by
        unfold IsRen; intro i
        exists (r i); apply Or.inl
        simp [Ren.to]

      theorem cons_re {σ : Subst T} k : IsRen σ -> IsRen (.re k :: σ) := by
        intro h; unfold IsRen at *; intro i
        cases i <;> simp
        case _ i =>
          replace h := h i
          cases h; case _ x h =>
          cases h
          case _ h => exists x; simp [*]
          case _ h => exists x; simp [*]

      theorem cons_su {σ : Subst T} k : IsRen σ -> IsRen (.su (HasSimpleVar.var k) :: σ) := by
        intro h; unfold IsRen at *; intro i
        cases i <;> simp
        case _ => exists k
        case _ i =>
          replace h := h i
          cases h; case _ x h =>
          cases h
          case _ h => exists x; simp [*]
          case _ h => exists x; simp [*]

      theorem lift {σ : Subst T} : IsRen σ -> IsRen σ.lift := by
        intro h i
        cases i <;> (unfold Subst.lift; simp at *)
        case _ i =>
          generalize zdef : σ i = z
          cases z <;> simp at *
          case _ t =>
            replace h := h i
            cases h; case _ k h =>
            cases h
            case _ h => rw [zdef] at h; injection h
            case _ h =>
              rw [zdef] at h; injection h with e
              subst e; rw [HasSimpleVar.ren]
              exists (k + 1)

      theorem compose {σ τ : Subst T} : IsRen σ -> IsRen τ -> IsRen (σ ∘ τ) := by
        intro h1 h2
        unfold IsRen at *; intro i
        unfold Subst.compose; simp
        replace h1 := h1 i
        cases h1; case _ k h1 =>
        cases h1
        case _ h1 =>
          rw [h1]; simp
          apply h2 k
        case _ h1 =>
          rw [h1]; simp
          replace h2 := h2 k
          cases h2; case _ z h2 =>
          cases h2
          case _ h2 => rw [h2]; simp; exists z
          case _ h2 => rw [h2]; simp; exists z
    end
  end IsRen
end LeanSubst
