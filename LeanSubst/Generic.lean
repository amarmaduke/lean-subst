
-- universe u u1 u2 u3 u4

-- class SyntaxStructure (Ctx : Type u1) (S : Ctx -> Type u2) where
--   Var : Ctx -> Type u2
--   Ren : (Ctx -> Type u2) -> Ctx -> Ctx -> Sort u3
--   Lift : (Ctx -> Ctx -> Sort u3) -> Ctx -> Ctx -> Sort u3
--   rlift {Γ Δ : Ctx} : Ren Var Γ Δ -> Lift (Ren Var) Γ Δ
--   rmap {Γ Δ : Ctx} (r : Ren Var Γ Δ) : Ren S Γ Δ



-- inductive Ty where
-- | base : Ty
-- | arrow : Ty -> Ty -> Ty

-- notation "★" => Ty.base
-- infixr:78 " -:> " => Ty.arrow

-- inductive Var : List Ty -> Ty -> Type where
-- | here {Γ A} : Var (A::Γ) A
-- | there {Γ A B} : Var Γ B -> Var (A::Γ) B

-- inductive Term : List Ty -> Ty -> Type where
-- | var {Γ T} :
--   Var Γ T ->
--   Term Γ T
-- | lam {Γ A B} :
--   Term (A::Γ) B ->
--   Term Γ (A -:> B)
-- | app {Γ A B} :
--   Term Γ (A -:> B) ->
--   Term Γ A ->
--   Term Γ B

-- instance : SyntaxStructure (List Ty) ((A : Ty) -> Term · A) where
--   Var Γ := (A : Ty) -> Var Γ A
--   Ren F Γ Δ := {A : Ty} -> F Γ -> F Δ
--   Lift

-- open SyntaxStructure

-- class RenMap [SyntaxStructure] (S : Ctx Idx -> Idx -> Type u3) where
--   rmap {Γ Δ : Ctx Idx} (r : Ren Γ Δ) {T : Idx} : S Γ T -> S Δ T
