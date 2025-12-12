
-- namespace Subst
--   @[simp, coe]
--   def coe [Coe A B] : Subst A -> Subst B
--   | σ, n => σ n

--   class CommutesWithSmap (A B) [SubstMap A] [SubstMap B] [c : Coe A B] where
--     coe_commutes : ∀ a (σ : Subst A), Coe.coe (a[σ]) = (Coe.coe a)[@coe _ _ c σ]

--   @[simp]
--   theorem coe_cons {a : Subst.Action A} {σ : Subst A} [Coe A B]
--     : coe (a :: σ) = ↑a :: (coe (B := B) σ)
--   := by
--     funext; case _ x =>
--     simp; cases x <;> simp

--   @[simp]
--   theorem coe_comp {σ τ : Subst A}
--     [SubstMap A] [SubstMap B] [Coe A B] [i : CommutesWithSmap A B]
--     : coe (σ ∘ τ) = coe (B := B) σ ∘ coe τ
--   := by
--     funext; case _ x =>
--     simp [Subst.compose]
--     generalize zdef : σ x = z at *
--     cases z <;> simp
--     case _ a =>
--       rw [CommutesWithSmap.coe_commutes]
-- end Subst
