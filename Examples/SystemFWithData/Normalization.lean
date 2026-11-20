
import LeanSubst
import Examples.SystemFWithData.Typing
import Examples.SystemFWithData.Model

open LeanSubst

namespace SystemFWithData

def SemSet := List Ty -> Ty -> Term -> Prop
def SemRel := List Ty -> Ty -> Term -> Term -> Prop

def Kripke (S : SemSet) : SemSet
| Γ, A, t => ∀ {r1 Δ}, Γ -⟨r1⟩> Δ -> (r2 : Ren Ty) -> S Δ A⟨r2⟩ t⟨r1, r2⟩

mutual
  inductive SnNor : SemSet -> SemSet
  | lam (S : Ty -> SemSet) {T Γ A B t} :
    Kripke (S $ A -:> B) Γ (A -:> B) (λ[A] t) ->
    SnNor (S B) (A::Γ) B t ->
    T = S (A -:> B) ->
    SnNor T Γ (A -:> B) (λ[A] t)
  | tlam (S : Ty -> SemSet) {T Γ P t} :
    Kripke (S $ `∀ P) Γ (`∀ P) (Λ t) ->
    SnNor (S $ P) Γ⟨.add Ty 1⟩ P t ->
    T = S (`∀ P) ->
    SnNor T Γ (`∀ P) (Λ t)
  | neu {S Γ A t} : SnNeu S Γ A t -> SnNor S Γ A t
  | red {S Γ A t t'} :
    SnRed S Γ A t t' ->
    SnNor S Γ A t' ->
    SnNor S Γ A t

  inductive SnNeu : SemSet -> SemSet
  | var (S : Ty -> SemSet) {T Γ A x} :
    Γ[x]? = some A ->
    T = S A ->
    SnNeu T Γ A #x
  | app (S : Ty -> SemSet) {T Γ A B f a} :
    SnNeu (S $ A -:> B) Γ (A -:> B) f ->
    SnNor (S A) Γ A a ->
    T = S B ->
    SnNeu T Γ B (f `• a)
  | tapp (S : Ty -> SemSet) {T Γ P P' f A} :
    SnNeu (S $ `∀ P) Γ (`∀ P) f ->
    P' = P[su A .: 𝐬0] ->
    T = S P' ->
    SnNeu T Γ P' (f •[A])

  inductive SnRed : SemSet -> SemRel
  | beta (S : Ty -> SemSet) {T Γ A B b t} :
    SnNor (S A) Γ A t ->
    T = S B ->
    SnRed T Γ B ((λ[A] b) `• t) b[su t .: 𝐬0, .id Ty]
  | tbeta (S : Ty -> SemSet) {T Γ P b t} :
    T = S P ->
    SnRed T Γ P ((Λ b) •[t]) b[.id Term, su t .: 𝐬0]
  | step_app (S : Ty -> SemSet) {T Γ A B f a f'} :
    SnRed (S $ A -:> B) Γ (A -:> B) f f' ->
    T = S B ->
    SnRed T Γ B (f `• a) (f' `• a)
  | step_tapp (S : Ty -> SemSet) {T Γ P P' f A f'} :
    SnRed (S $ `∀ P) Γ (`∀ P) f f' ->
    P' = P[su A .: 𝐬0] ->
    T = S P' ->
    SnRed T Γ P' (f •[A]) (f' •[A])
end

mutual
  theorem SnNor.rename {S : Ty -> SemSet} {T Γ Δ A t r1}
    (mr : Γ -⟨r1⟩> Δ) (r2 : Ren Ty) (e1 : T = S A)
    : SnNor T Γ A t -> SnNor (S A⟨r2⟩) Δ⟨r2⟩ A⟨r2⟩ t⟨r1, r2⟩
  | .lam (A := C) (B := B) S' j1 j2 e2 =>
    have lem := @SnNor.rename S' _ _ _ B _ _ (mr.lift [C]) r2 rfl j2
    .lam S' sorry (lem %simp) (by simp; sorry)
  | _ => sorry

  theorem SnNeu.rename {S Γ Δ A t r1} (mr : Γ -⟨r1⟩> Δ) (r2 : Ren Ty)
    : SnNeu S Γ A t -> SnNeu S Δ A⟨r2⟩ t⟨r1, r2⟩
  := sorry

  theorem SnRed.rename {S Γ Δ A t t' r1} (mr : Γ -⟨r1⟩> Δ) (r2 : Ren Ty)
    : SnRed S Γ A t t' -> SnRed S Δ A⟨r2⟩ t⟨r1, r2⟩ t'⟨r1, r2⟩
  := sorry
end

-- @[simp]
-- instance : Model SemSet where
--   Arrow A B := fun
--     | Γ, A' -:> B', λ[_] t =>
--       ∀ (a : Action Term), SnNor A Γ A' a -> SnNor B Γ B' t[a .: 𝐬0, .id Ty]
--     | _, _, _ => False
--   All P := fun
--     | Γ, `∀ P', Λ t =>
--       ∀ (A : SemSet) (a : Action Ty), SnNor (P A) Γ P'[a .: .id Ty] t[.id Term, a .: 𝐬0]
--     | _, _, _ => False

-- @[simp]
-- def 𝒱 (A : Ty) (ξ : Nat -> SemSet) := ⟦ A ⟧ ξ

-- @[simp]
-- def ℰ Γ A ξ := SnNor (𝒱 A ξ) Γ A

-- structure SemSubst (Γ Δ : List Ty) (ξ : Nat -> SemSet) (σ : Subst Term) (τ : Subst Ty) where
--   act : ∀ {i} {T : Ty}, Γ[i]? = some T -> ℰ Δ[τ] T[τ] ξ (σ.act i)

-- notation:35 Γ:35 " -⟦" σ "," τ ";" ξ "⟧> " Δ:35 => SemSubst Γ Δ ξ σ τ

-- @[simp]
-- def SemTyping (Γ : List Ty) (t : Term) (A : Ty) :=
--   ∀ {σ ξ Δ} (τ : Subst Ty), Γ -⟦σ,τ;ξ⟧> Δ -> ℰ Δ[τ] A[τ] ξ t[σ, τ]

-- notation:60 Γ:60 " ⊨ " t:60 " : " A:60 => SemTyping Γ t A

-- theorem SemSubst.id {Γ} τ ξ : Γ -⟦.id Term, τ ; ξ⟧> Γ :=
--   ⟨λ h => .neu (.var $ by norm_subst; rw [<-h])⟩

-- theorem SemSubst.lift {Γ Δ σ τ ξ} (m : Γ -⟦σ,τ;ξ⟧> Δ) A : A::Γ -⟦σ.lift [Ty],τ;ξ⟧> A::Δ := sorry

-- theorem SemSubst.lift_ty {Γ Δ σ τ ξ} (m : Γ -⟦σ,τ;ξ⟧> Δ)
--   : Γ⟨.add Ty 1⟩ -⟦σ >> ·⟨.id Term, .add Ty 1⟩, τ.lift; ξ⟧> Δ⟨.add Ty 1⟩
-- := sorry

-- theorem ℰ.rename {Γ Δ A ξ t r1} (mr : Γ -⟨r1⟩> Δ) (r2 : Ren Ty) (j : ℰ Γ A ξ t)
--   : ℰ Δ A⟨r2⟩ ξ t⟨r1, r2⟩
-- := by
--   simp_all
--   have lem := j.rename mr r2
--   sorry

-- theorem SemSubst.rename {Γ Δ Ξ σ τ ξ r1}
--   (m1 : Γ -⟦σ,τ;ξ⟧> Δ) (r2 : Ren Ty) (m2 : Δ[τ] -⟨r1⟩> Ξ[τ >> ·⟨r2⟩])
--   : Γ -⟦σ >> ·⟨r1, r2⟩, τ >> ·⟨r2⟩; ξ⟧> Ξ
-- := ⟨λ {i T} h => (m1.act h).rename m2 r2 %simp⟩

-- theorem SemSubst.weaken {Γ Δ σ τ ξ} A (m : Γ -⟦σ,τ;ξ⟧> Δ) : Γ⟨.add Ty 1⟩ -⟦σ, τ; A .: ξ⟧> Δ := sorry


-- theorem ℰ.app {S Δ T A B ξ f a}
--   (e1 : S = 𝒱 (A -:> B) ξ) (e2 : T = A -:> B)
--   (j1 : ℰ Δ A ξ a)
--   : SnNor S Δ T f -> ℰ Δ B ξ (f `• a)
-- | .lam j1 j2 => sorry
-- | .neu j => sorry
-- | .red j1 j2 => sorry

-- theorem ℰ.tapp {S Δ T P ξ f} (A : Ty)
--   (e1 : S = 𝒱 (`∀ P) ξ) (e2 : T = `∀ P)
--   : SnNor S Δ T f -> ℰ Δ P[su A .: 𝐬0] ξ (f •[A])
-- | .tlam j1 j2 => sorry
-- | .neu j => sorry
-- | .red j1 j2 => sorry

-- -- theorem ℰ.tlam {Δ P ξ t} (j : Kripke (𝒱 (`∀ P) ξ) Δ (`∀ P) (Λ t))
-- --   : ℰ Δ (`∀ P) ξ (Λ t)
-- -- := sorry

-- theorem Typing.fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨ t : A
-- | var j, σ, ξ, Δ, τ, mσ => mσ.act j
-- | lam (A := A') (B := B) (t := t) j, σ, ξ, Δ, τ, mσ =>
--   have lem : Kripke (𝒱 (A' -:> B)[τ] ξ) Δ[τ] (A' -:> B)[τ] (λ[A'] t)[σ, τ] := λ {r Ξ} mr r2 {C} c =>
--     by simp_all; sorry
--     -- have tj' := ⟦tj⟧ (.su aj $ mσ.comp mr)
--     -- by simp; norm_subst; exact tj'
--   .lam lem (j.fundamental τ (mσ.lift A') %simp)
-- | app j1 j2, σ, ξ, Δ, τ, mσ => ℰ.app rfl rfl (j2.fundamental τ mσ) (j1.fundamental τ mσ)
-- | tlam (P := P) (t := t) j, σ, ξ, Δ, τ, mσ =>
--   have lem : Kripke (𝒱 (`∀ P)[τ] ξ) Δ[τ] (`∀ P)[τ] (Λ t)[σ, τ] := λ {r Ξ} mr r2 {C} c =>
--     have mμ := (mσ.weaken C).rename mr r2
--     have j' := j.fundamental (τ >> ·⟨r2⟩) mμ
--     by simp_all; rw [<-Model.subst]; sorry
--   .tlam lem (j.fundamental τ.lift (mσ.lift_ty) %simp)
-- | tapp (A := C) j e, σ, ξ, Δ, τ, mσ => ℰ.tapp C[τ] rfl rfl (j.fundamental τ mσ) %simp [e]

-- mutual
--   theorem SnNor.consistency {S Γ T t x} (e1 : Γ = []) (e2 : T = t#x) : ¬ SnNor S Γ T t
--   | .lam j1 j2 => by injection e2
--   | .neu j => j.consistency e1
--   | .red j1 j2 => j2.consistency e1 e2

--   theorem SnNeu.consistency {S Γ T t} (e : Γ = []) : ¬ SnNeu S Γ T t
--   | .var j => by simp_all
--   | .app j _ | .tapp j _ => j.consistency e
-- end

-- theorem SnNor.consistency_all {S Γ T t} (e1 : Γ = []) (e2 : T = `∀ t#0) : ¬ SnNor S Γ T t
-- | .tlam j1 j2 => j2.consistency (x := 0) (by simp [e1]) (by injection e2)
-- | .neu j => j.consistency e1
-- | .red j1 j2 => j2.consistency_all e1 e2

-- theorem Typing.consistency {t} : ¬ ([] ⊢ t : (`∀ t#0)) :=
--   have ξ : Nat -> SemSet := λ _ _ _ _ => False
--   λ j => SnNor.consistency_all rfl rfl (j.fundamental (.id Ty) (.id (.id Ty) ξ))

end SystemFWithData
