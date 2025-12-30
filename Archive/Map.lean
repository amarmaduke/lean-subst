import LeanSubst.Basic

-- namespace LeanSubst.Subst
--   section
--     variable {A : Type} {B : Type} {f : A -> B}

--     @[simp]
--     def map {A B} (f : A -> B) : Subst A -> Subst B
--     | σ, n =>
--       match (σ n) with
--       | .su t => .su (f t)
--       | .re k => .re k

--     @[simp]
--     theorem map_rename_seq {k} {σ : Subst A} : map f (.re k :: σ) = .re k :: map f σ := by
--       funext; case _ x =>
--       cases x <;> simp

--     @[simp]
--     theorem map_replace_seq {t} {σ : Subst A} : map f (.su t :: σ) = .su (f t) :: map f σ := by
--       funext; case _ x =>
--       cases x <;> simp

--     @[simp]
--     theorem map_rename_noop {r : Ren} : map f r.to = r.to := by
--       funext; case _ x =>
--       unfold Ren.to
--       cases x <;> simp

--     @[simp]
--     theorem map_I_noop : map f +0 = +0 := by apply map_rename_noop

--     @[simp]
--     theorem map_S_noop : map f +1 = +1 := by apply map_rename_noop

--     theorem map_rename_compose_left {τ : Subst A} [SubstMap A] [SubstMap B] {f : A -> B} {r : Ren}
--       : (∀ t, f t[r.to] = (f t)[r.to]) -> map f (τ ∘ r.to) = (map f τ) ∘ r.to
--     := by
--       intro h
--       unfold Subst.compose; simp
--       funext; case _ x =>
--       simp; generalize zdef : τ x = z at *
--       cases z <;> simp
--       case _ k => unfold Ren.to; simp
--       case _ t => apply h

--     @[simp]
--     theorem map_rename_compose_right {σ : Subst A} [SubstMap A] [SubstMap B] {f : A -> B} {r : Ren}
--       : map f (r.to ∘ σ) = r.to ∘ (map f σ)
--     := by
--       unfold Subst.compose; simp
--       funext; case _ x =>
--         unfold Ren.to; simp

--     theorem map_S_compose_left {τ : Subst A} [SubstMap A] [SubstMap B] {f : A -> B}
--       : (∀ t, f t[+1] = (f t)[+1]) -> map f (τ ∘ +1) = (map f τ) ∘ +1
--     := by
--       intro h
--       apply map_rename_compose_left h

--     @[simp]
--     theorem map_S_compose_right {σ : Subst A} [SubstMap A] [SubstMap B] {f : A -> B}
--       : map f (+1 ∘ σ) = +1 ∘ (map f σ)
--     := by apply map_rename_compose_right
--   end
-- end LeanSubst.Subst
