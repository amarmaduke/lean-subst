
import Examples.SystemT.Term
open LeanSubst

namespace SystemT

section
set_option quotPrecheck false in
set_option hygiene false in
local notation:60 Γ:60 " ⊢ " t:60 " : " A:60 => Typing Γ t A

inductive Typing : List Ty -> Term -> Ty -> Prop where
| var {Γ x A} :
  Γ[x]? = some A ->
  Γ ⊢ #x : A
| lam {Γ A B t} :
  A::Γ ⊢ t : B ->
  Γ ⊢ λ[A] t : A -:> B
| app {Γ A B f a} :
  Γ ⊢ f : A -:> B ->
  Γ ⊢ a : A ->
  Γ ⊢ f `• a : B
| unit {Γ} :
  Γ ⊢ `() : ⊤
| pair {Γ A B t s} :
  Γ ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ `⟨t,s⟩ : A `× B
| fst {Γ A B t} :
  Γ ⊢ t : A `× B ->
  Γ ⊢ t.!1 : A
| snd {Γ A B t} :
  Γ ⊢ t : A `× B ->
  Γ ⊢ t.!2 : B
| absurd {Γ T t} :
  Γ ⊢ t : ⊥ ->
  Γ ⊢ .absurd T t : T
| split {Γ A B C t l r} :
  Γ ⊢ t : A `+ B ->
  A::Γ ⊢ l : C ->
  B::Γ ⊢ r : C ->
  Γ ⊢ .split t l r : C
| inj1 {Γ A B t} :
  Γ ⊢ t : A ->
  Γ ⊢ .inj B 1 t : A `+ B
| inj2 {Γ A B t} :
  Γ ⊢ t : B ->
  Γ ⊢ .inj A 2 t : A `+ B
| zero {Γ} :
  Γ ⊢ `0 : ℕ
| succ {Γ t} :
  Γ ⊢ t : ℕ ->
  Γ ⊢ t `+1 : ℕ
| nrec {Γ T n z s} :
  Γ ⊢ n : ℕ ->
  Γ ⊢ z : T ->
  ℕ::T::Γ ⊢ s : T ->
  Γ ⊢ .nrec n z s : T
end

notation:60 Γ:60 " ⊢ " t:60 " : " A:60 => Typing Γ t A

structure TypingRen (r : Ren Term) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ Δ : List Ty} A {r : Ren Term} (h : Γ -⟨r⟩> Δ) : A::Γ -⟨r.lift⟩> A::Δ :=
  ⟨λ {x} _ j =>
    match x with
    | 0 => j
    | _ + 1 => h.act j⟩

theorem TypingRen.id {X} : X -⟨.id Term⟩> X := ⟨λ h => h⟩

theorem TypingRen.succ {A X} : X -⟨.add Term 1⟩> A::X := ⟨λ h => h⟩

theorem TypingRen.comp {X Y Z} {r1 r2 : Ren Term} : X -⟨r1⟩> Y -> Y -⟨r2⟩> Z -> X -⟨r1 >> r2⟩> Z :=
  λ j1 j2 => ⟨λ h => j2.act (j1.act h)⟩

theorem Typing.rename {Γ Δ t A} {r : Ren Term} (m : Γ -⟨r⟩> Δ) : Γ ⊢ t : A -> Δ ⊢ t⟨r⟩ : A
| var h => var (m.act h)
| lam (A := C) t => lam (t.rename (m.lift C))
| app f a => app (f.rename m) (a.rename m)
| unit => sorry
| pair t s => sorry
| fst t => sorry
| snd t => sorry
| absurd t => sorry
| split t l r => sorry
| inj1 t => sorry
| inj2 t => sorry
| zero => sorry
| succ t => sorry
| nrec n z s => sorry

structure TypingSubst (σ : Subst Term) (Γ Δ : List Ty) where
  act : ∀ {x : Nat} {T}, Γ[x]? = some T -> Δ ⊢ σ.act x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

theorem TypingSubst.succ {A X} : X -[.add Term 1]> A::X := ⟨λ h => .var h⟩

theorem TypingSubst.re {Γ Δ A y σ} (j : Δ[y]? = some A) (m : Γ -[σ]> Δ) : A::Γ -[re y.:σ]> Δ :=
  ⟨λ {x} T h =>
    match x with
    | 0 =>
      have h : A = T := by grind
      .var $ j %simp [h]
    | _ + 1 => m.act h⟩

theorem TypingSubst.su {Γ Δ A a σ} (j : Δ ⊢ a : A) (m : Γ -[σ]> Δ) : A::Γ -[su a.:σ]> Δ :=
  ⟨λ {x} T h =>
    match x with
    | 0 =>
      have h : A = T := by grind
      j %simp [h]
    | _ + 1 => m.act h⟩

theorem TypingSubst.lift {Γ Δ : List Ty} A {σ : Subst Term} (m : Γ -[σ]> Δ) : A::Γ -[σ.lift]> A::Δ :=
  ⟨λ {x} _ h =>
    match x with
    | 0 => .var h
    | _ + 1 => Typing.rename (Δ := A::Δ) .succ (m.act h) %simp⟩

theorem Typing.subst {Γ Δ t A} {σ : Subst Term}  (m : Γ -[σ]> Δ) : Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| var h => m.act h
| lam (A := C) t => lam (t.subst (m.lift C))
| app f a => app (f.subst m) (a.subst m)
| unit => sorry
| pair t s => sorry
| fst t => sorry
| snd t => sorry
| absurd t => sorry
| split t l r => sorry
| inj1 t => sorry
| inj2 t => sorry
| zero => sorry
| succ t => sorry
| nrec n z s => sorry

theorem Typing.beta {Γ A B b t} (j1 : (A::Γ) ⊢ b : B) (j2 : Γ ⊢ t : A) : Γ ⊢ b[su t .: 𝐬0] : B :=
  Typing.subst
    ⟨λ {x} T h =>
      match x with
      | 0 =>
        have h : A = T := by grind
        j2 %simp [h]
      | _ + 1 => .var h⟩
    j1

end SystemT
