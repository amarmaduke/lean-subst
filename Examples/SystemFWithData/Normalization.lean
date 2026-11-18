
import LeanSubst
import Examples.SystemFWithData.Typing
import Examples.SystemFWithData.Model

open LeanSubst

namespace SystemFWithData

def SemSet := List Ty -> Ty -> Term -> Prop
def SemRel := List Ty -> Ty -> Term -> Term -> Prop

def Kripke (S : SemSet) : SemSet
| Γ, A, t => ∀ {r1 Δ}, Γ -⟨r1⟩> Δ -> (r2 : Ren Ty) -> S Δ A t⟨r1, r2⟩

mutual
  inductive SnNor : SemSet -> SemSet
  | lam {S1 S2 Γ A B t} :
    Kripke S1 Γ (A -:> B) (λ[A] t) ->
    SnNor S2 (A::Γ) B t ->
    SnNor S1 Γ (A -:> B) (λ[A] t)
  | tlam {S1 S2 Γ P t} :
    Kripke S1 Γ (`∀ P) (Λ t) ->
    SnNor S2 Γ⟨.add Ty 1⟩ P t ->
    SnNor S1 Γ (`∀ P) (Λ t)
  | neu {S Γ A t} : SnNeu S Γ A t -> SnNor S Γ A t
  | red {S Γ A t t'} : SnRed S Γ A t t' -> SnNor S Γ A t' -> SnNor S Γ A t

  inductive SnNeu : SemSet -> SemSet
  | var {S Γ A x} : Γ[x]? = some A -> SnNeu S Γ A #x
  | app {S1 S2 S3 Γ A B f a} : SnNeu S1 Γ (A -:> B) f -> SnNor S2 Γ A a -> SnNeu S3 Γ B (f `• a)
  | tapp {S1 S2 Γ P P' f A} : SnNeu S1 Γ (`∀ P) f -> P' = P[su A .: 𝐬0] -> SnNeu S2 Γ P' (f •[A])

  inductive SnRed : SemSet -> SemRel
  | beta {S1 S2 Γ A B b t} : SnNor S1 Γ A t -> SnRed S2 Γ B ((λ[A] b) `• t) b[su t .: 𝐬0, .id Ty]
  | tbeta {S Γ P b t} : SnRed S Γ P ((Λ b) •[t]) b[.id Term, su t .: 𝐬0]
  | step_app {S1 S2 Γ A B f a f'} : SnRed S1 Γ (A -:> B) f f' -> SnRed S2 Γ B (f `• a) (f' `• a)
  | step_tapp {S1 S2 Γ P P' f A f'} :
    SnRed S1 Γ (`∀ P) f f' ->
    P' = P[su A .: 𝐬0] ->
    SnRed S2 Γ P' (f •[A]) (f' •[A])
end

@[simp]
instance : Model SemSet where
  Arrow A B := fun
    | Γ, A' -:> B', λ[_] t =>
      ∀ (a : Action Term), SnNor A Γ A' a -> SnNor B Γ B' t[a .: 𝐬0, .id Ty]
    | _, _, _ => False
  All P := fun
    | Γ, `∀ P', Λ t =>
      ∀ (A : SemSet) (a : Action Ty), SnNor (P A) Γ P'[a .: .id Ty] t[.id Term, a .: 𝐬0]
    | _, _, _ => False

@[simp]
def 𝒱 (A : Ty) (ξ : Nat -> SemSet) := ⟦A⟧ ξ

@[simp]
def ℰ Γ A ξ := SnNor (𝒱 A ξ) Γ A

structure SemSubst (Γ Δ : List Ty) (ξ : Nat -> SemSet) (σ : Subst Term) (τ : Subst Ty) where
  act : ∀ {i} {T : Ty}, Γ[i]? = .some T -> ℰ Δ[τ] T[τ] ξ (σ.act i)

notation:35 Γ:35 " -⟦" σ "," τ ";" ξ "⟧> " Δ:35 => SemSubst Γ Δ ξ σ τ

@[simp]
def SemTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ ξ Δ} (τ : Subst Ty), Γ -⟦σ,τ;ξ⟧> Δ -> ℰ Δ[τ] A[τ] ξ t[σ, τ]

notation:60 Γ:60 " ⊨ " t:60 " : " A:60 => SemTyping Γ t A

theorem SemSubst.id {Γ} τ ξ : Γ -⟦.id Term, τ ; ξ⟧> Γ :=
  ⟨λ h => .neu (.var $ by norm_subst; rw [<-h])⟩

theorem SemSubst.lift {Γ Δ σ τ ξ} (m : Γ -⟦σ,τ;ξ⟧> Δ) A : A::Γ -⟦σ.lift [Ty],τ;ξ⟧> A::Δ := sorry

theorem SemSubst.lift_ty {Γ Δ σ τ ξ} (m : Γ -⟦σ,τ;ξ⟧> Δ)
  : Γ⟨.add Ty 1⟩ -⟦σ >> ·⟨.id Term, .add Ty 1⟩, τ.lift; ξ⟧> Δ⟨.add Ty 1⟩
:= sorry


-- theorem SemSubst.comp {Γ Δ Ξ σ ξ r} (m1 : Γ -⟦σ;ξ⟧> Δ) (m2 : Δ -⟨r⟩> Ξ) : Γ -⟦σ >> ·⟨r⟩;ξ⟧> Ξ := sorry


theorem ℰ.app {S Δ T A B ξ f a}
  (e1 : S = 𝒱 (A -:> B) ξ) (e2 : T = A -:> B)
  (j1 : ℰ Δ A ξ a)
  : SnNor S Δ T f -> ℰ Δ B ξ (f `• a)
| .lam j1 j2 => sorry
| .neu j => sorry
| .red j1 j2 => sorry

theorem ℰ.tapp {S Δ T P ξ f} (A : Ty)
  (e1 : S = 𝒱 (`∀ P) ξ) (e2 : T = `∀ P)
  : SnNor S Δ T f -> ℰ Δ P[su A .: 𝐬0] ξ (f •[A])
| .tlam j1 j2 => sorry
| .neu j => sorry
| .red j1 j2 => sorry

theorem Typing.fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨ t : A
| var j, σ, ξ, Δ, τ, mσ => mσ.act j
| lam (A := A') (B := B) (t := t) j, σ, ξ, Δ, τ, mσ =>
  have lem : Kripke (𝒱 (A' -:> B)[τ] ξ) Δ[τ] (A' -:> B)[τ] (λ[A'] t)[σ, τ] := λ {r Ξ} mr {a} aj =>
    sorry
    -- have tj' := ⟦tj⟧ (.su aj $ mσ.comp mr)
    -- by simp; norm_subst; exact tj'
  .lam lem (j.fundamental τ (mσ.lift A') %simp)
| app j1 j2, σ, ξ, Δ, τ, mσ => ℰ.app rfl rfl (j2.fundamental τ mσ) (j1.fundamental τ mσ)
| tlam (P := P) (t := t) j, σ, ξ, Δ, τ, mσ =>
  have lem : Kripke (𝒱 (`∀ P)[τ] ξ) Δ[τ] (`∀ P)[τ] (Λ t)[σ, τ] := λ {r Ξ} mr {a} aj =>
    sorry
  .tlam lem (j.fundamental τ.lift (mσ.lift_ty) %simp)
| tapp (A := C) j e, σ, ξ, Δ, τ, mσ => ℰ.tapp C[τ] rfl rfl (j.fundamental τ mσ) %simp [e]

mutual
  theorem SnNor.consistency {S Γ T t x} (e1 : Γ = []) (e2 : T = t#x) : ¬ SnNor S Γ T t
  | .lam j1 j2 => by injection e2
  | .neu j => j.consistency e1
  | .red j1 j2 => j2.consistency e1 e2

  theorem SnNeu.consistency {S Γ T t} (e : Γ = []) : ¬ SnNeu S Γ T t
  | .var j => by simp_all
  | .app j _ | .tapp j _ => j.consistency e
end

theorem SnNor.consistency_all {S Γ T t} (e1 : Γ = []) (e2 : T = `∀ t#0) : ¬ SnNor S Γ T t
| .tlam j1 j2 => j2.consistency (x := 0) (by simp [e1]) (by injection e2)
| .neu j => j.consistency e1
| .red j1 j2 => j2.consistency_all e1 e2

theorem Typing.consistency {t} : ¬ ([] ⊢ t : (`∀ t#0)) :=
  have ξ : Nat -> SemSet := λ _ _ _ _ => False
  λ j => SnNor.consistency_all rfl rfl (j.fundamental (.id Ty) (.id (.id Ty) ξ))

end SystemFWithData
