
import LeanSubst
import Examples.SystemFWithData.Typing

open LeanSubst

universe u u1 u2 u3
variable {D : Sort u}

namespace SystemFWithData

class Model (D : Sort u) where
  Arrow : D -> D -> D
  All : (D -> D) -> D

section
set_option quotPrecheck false in
set_option hygiene false in
local notation "⟦ " t " ⟧ " ξ:100 => Model.int_ty ξ t

@[simp]
def Model.int_ty [Model D] (ξ : Nat -> D) : Ty -> D
| t#x => ξ x
| A -:> B => Arrow (⟦ A ⟧ ξ) (⟦ B ⟧ ξ)
| `∀ P => All (λ d => ⟦ P ⟧ (d .: ξ))
end
notation "⟦ " t " ⟧ " ξ:100 => Model.int_ty ξ t

@[simp]
def Model.int_subst [Model D] (ξ : Nat -> D) (σ : Subst Ty) : Nat -> D
| i => ⟦σ.act i⟧ ξ

notation "⟦ " σ " ⟧ " ξ:100 => Model.int_subst ξ σ

-- @[simp]
-- theorem Model.rename [Model D] {ξ : Nat -> D} (r : Ren Ty)
--   : {A : Ty} -> ⟦ A⟨r⟩ ⟧ ξ = ⟦ A ⟧ (ξ ∘ r.act)
-- | t#x => by simp
-- | A -:> B => by simp [@rename _ ξ r A, @rename _ ξ r B]
-- | `∀ P =>
--   have lem {d} : ⟦ P⟨r.lift⟩ ⟧ (d .: ξ) = ⟦ P ⟧ (d .: ξ ∘ r.act) := by
--     have e := @rename _ (d .: ξ) r.lift P
--     rw [e]; simp; sorry
--   by simp_all

-- @[simp]
-- theorem Model.subst [Model D] {ξ : Nat -> D} (σ : Subst Ty)
--   : {A : Ty} -> ⟦ A[σ] ⟧ ξ = ⟦ A ⟧ (⟦ σ ⟧ ξ )
-- | t#x => sorry
-- | A -:> B => sorry
-- | `∀ P => sorry

end SystemFWithData
