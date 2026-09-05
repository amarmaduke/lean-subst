
import Examples.STLC.Term
open LeanSubst

namespace STLC

inductive Red : Term -> Term -> Prop where
| beta {A b t} : Red (.app (λ[A] b) t) (b[su t::𝐬0])
| app1 {f f' a} : Red f f' -> Red (.app f a) (.app f' a)
| app2 {a a' f} : Red a a' -> Red (.app f a) (.app f a')
| lam {A t t'} : Red t t' -> Red (λ[A] t) (λ[A] t')

inductive Typing : List Ty -> Term -> Ty -> Prop where
| var {Γ x A} :
  Γ[x]? = some A ->
  Typing Γ #x A
| lam {Γ A B t} :
  Typing (A::Γ) t B ->
  Typing Γ (λ[A] t) (A -:> B)
| app {Γ A B f a} :
  Typing Γ f (A -:> B) ->
  Typing Γ a A ->
  Typing Γ (.app f a) B

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

structure TypingRen (r : Ren Term) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ Δ : List Ty} A {r : Ren Term} (h : Γ -⟨r⟩> Δ) : A::Γ -⟨r.lift⟩> A::Δ :=
  ⟨λ {x} _ j =>
    match x with
    | 0 => j
    | _ + 1 => h.act j⟩

theorem TypingRen.id {X} : X -⟨.id Term⟩> X := ⟨λ h => h⟩

theorem TypingRen.succ {A X} : X -⟨.succ Term⟩> A::X := ⟨λ h => h⟩

theorem TypingRen.comp {X Y Z} {r1 r2 : Ren Term} : X -⟨r1⟩> Y -> Y -⟨r2⟩> Z -> X -⟨r1 >> r2⟩> Z :=
  λ j1 j2 => ⟨λ h => j2.act (j1.act h)⟩

theorem Typing.rename {Γ Δ t A} {r : Ren Term} (m : Γ -⟨r⟩> Δ) : Γ ⊢ t : A -> Δ ⊢ t⟨r⟩ : A
| var h => var (m.act h)
| app f a => app (f.rename m) (a.rename m)
| lam (A := C) t => lam (t.rename (m.lift C))

structure TypingSubst (σ : Subst Term) (Γ Δ : List Ty) where
  act : ∀ {x : Nat} {T}, Γ[x]? = some T -> Δ ⊢ σ.act x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

theorem TypingSubst.succ {A X} : X -[.succ Term]> A::X := ⟨λ h => .var h⟩

theorem TypingSubst.re {Γ Δ A y σ} (j : Δ[y]? = some A) (m : Γ -[σ]> Δ) : A::Γ -[re y::σ]> Δ :=
  mk (λ {x} _ h =>
    match x with
    | 0 => .var $ j |> cast (by simp at h; rw [h])
    | _ + 1 => m.act h)

theorem TypingSubst.su {Γ Δ A a σ} (j : Δ ⊢ a : A) (m : Γ -[σ]> Δ) : A::Γ -[su a::σ]> Δ :=
  mk (λ {x} _ h =>
    match x with
    | 0 => j |> cast (by simp; grind)
    | _ + 1 => m.act h)

theorem TypingSubst.lift {Γ Δ : List Ty} A {σ : Subst Term} (m : Γ -[σ]> Δ) : A::Γ -[σ.lift]> A::Δ :=
  ⟨λ {x} _ h =>
    match x with
    | 0 => .var h
    | _ + 1 =>
      let lem := Typing.rename (Δ := A::Δ) TypingRen.succ (m.act h)
      by simp at lem; exact lem⟩

theorem Typing.subst {Γ Δ t A} {σ : Subst Term}  (m : Γ -[σ]> Δ) : Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| var h => m.act h
| app f a => app (f.subst m) (a.subst m)
| lam (A := C) t => lam (t.subst (m.lift C))

theorem Typing.beta {Γ A B b t} (j1 : (A::Γ) ⊢ b : B) (j2 : Γ ⊢ t : A) : Γ ⊢ b[su t::.id Term] : B :=
  Typing.subst
    ⟨λ {x} _ h =>
      match x with
      | 0 => j2 |> cast (by simp at *; rw [h])
      | _ + 1 => .var h⟩
    j1

theorem Red.subst {t t'} {σ : Subst Term} : Red t t' -> Red t[σ] t'[σ]
| @Red.beta A b t => @Red.beta A b[σ.lift] t[σ] |> cast (by simp [Subst.rewrite_lift])
| .app1 r => .app1 r.subst
| .app2 r => .app2 r.subst
| .lam r => .lam r.subst

theorem Red.antirename' {s' t : Term} (r : Ren Term) : Red s' t -> ∀ s, s' = s⟨r⟩ -> ∃ z, Red s z ∧ t = z⟨r⟩
| @Red.beta A b t, .app (.lam A' b') t', h => ⟨b'[su t'::𝐬0], .beta, by simp_all⟩
| .app1 (f := f) d, .app f' a', h =>
  have ⟨z, d', e⟩ := d.antirename' r f' (by simp_all)
  ⟨.app z a', .app1 d', by simp_all⟩
| .app2 (a := a) d, .app f' a', h =>
  have ⟨z, d', e⟩ := d.antirename' r a' (by simp_all)
  ⟨.app f' z, .app2 d', by simp_all⟩
| .lam (t := t) d, .lam A' t', h =>
  have ⟨z, d', e⟩ := d.antirename' r.lift t' (by simp_all)
  ⟨.lam A' z, .lam d', by simp_all⟩

theorem Red.antirename {s t : Term} (r : Ren Term) (d : Red s⟨r⟩ t) : ∃ z, Red s z ∧ t = z⟨r⟩ :=
  Red.antirename' r d _ rfl

end STLC
