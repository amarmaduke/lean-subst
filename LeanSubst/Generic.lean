
-- universe u u1 u2 u3 u4

-- class SyntaxStructure {Ctx : Type u1} (S : Ctx -> Type u2) where
--   Var : Ctx -> Type u2
--   Ren : (Ctx -> Type u2) -> Ctx -> Ctx -> Sort u3
--   Lift : (Ctx -> Ctx -> Sort u3) -> Ctx -> Ctx -> Sort u3


-- class RenMap {Ctx : Type u1} (S : Ctx -> Type u2) [SyntaxStructure S] where
--   rlift {Γ Δ : Ctx} : Ren S (Var S) Γ Δ -> Lift S (Ren S (Var S)) Γ Δ
--   rmap {Γ Δ : Ctx} (r : Ren S (Var S) Γ Δ) : Ren S S Γ Δ

-- variable {Ctx : Type u1} (Var : Ctx -> Type u2) (S : Ctx -> Type u2)

-- def Ren (Γ Δ : Ctx) := Var Γ -> Var Δ

-- class RenMap {Ctx : Type u1} (Var S : Ctx -> Type u2) where
--   ext : Ctx -> Ctx
--   rlift {Γ Δ : Ctx} : Ren Var Γ Δ -> Ren Var Γ Δ

-- inductive Ty where
-- | base : Ty
-- | arrow : Ty -> Ty -> Ty

-- notation "★" => Ty.base
-- infixr:78 " -:> " => Ty.arrow

-- inductive TVar : List Ty -> Ty -> Type where
-- | here {Γ A} : TVar (A::Γ) A
-- | there {Γ A B} : TVar Γ B -> TVar (A::Γ) B

-- inductive Term : List Ty -> Ty -> Type where
-- | var {Γ T} :
--   TVar Γ T ->
--   Term Γ T
-- | lam {Γ A B} :
--   Term (A::Γ) B ->
--   Term Γ (A -:> B)
-- | app {Γ A B} :
--   Term Γ (A -:> B) ->
--   Term Γ A ->
--   Term Γ B

-- @[reducible, simp]
-- instance {A : Ty} : SyntaxStructure (Term · A) where
--   Var Γ := TVar Γ A
--   Ren F Γ Δ := F Γ -> F Δ
--   Lift F Γ Δ := ∀ {T}, F Γ Δ -> F (T::Γ) (T::Δ)

-- def Ren.lift {A : Ty} [SyntaxStructure (Term · A)] {Γ Δ : List Ty}
--   (r : Ren (Term · A) (TVar · A) Γ Δ) : Lift (Term · A) (Ren (Term · A) (Term · A)) Γ Δ
-- | .here => sorry
-- | .there x => .there (r x)

-- instance {A : Ty} : RenMap (Term · A) where
--   rlift r := fun
--   | _, .here => sorry
--   | _, .there => sorry




-- def Term.rmap {Γ Δ : List Ty} (r : Ren Γ Δ) {T : Ty} : Term Γ T -> Term Δ T
-- | var v => var (r v)
-- | lam t => lam (rmap (Ren.lift r) t)
-- | app f a => app (rmap r f) (rmap r a)


-- -- class RenMap [SyntaxStructure] (S : Ctx Idx -> Idx -> Type u3) where
-- --   rmap {Γ Δ : Ctx Idx} (r : Ren Γ Δ) {T : Idx} : S Γ T -> S Δ T
