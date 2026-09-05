
import Examples.STLC.Theory
open LeanSubst

namespace STLC

universe u

def Set (A : Sort u) := A -> Prop

def ℛ (S : Set Term) : Set Term
| t => ∀ (r:Ren Term), S t⟨r⟩

@[simp]
def is_lam : Term -> Bool
| .lam _ _ => true
| _ => false

inductive ℒ (S : Set Term) : Set Term where
| lift {t : Term} :
  (is_lam t -> ℛ S t) ->
  (∀ {t' : Term}, Red t t' -> ℒ S t') ->
  ℒ S t

def LR : Ty -> Set Term
| .base, t => SN Red t
| .arrow A B, .lam _ t => ∀ a, ℒ (LR A) a -> ℒ (LR B) t[su a::𝐬0]
| _, _ => False

def ℰ A := ℒ (LR A)

def 𝒞 (Γ : List Ty) (σ : Subst Term) : Prop :=
  ∀ {i : Nat} {T}, Γ[i]? = .some T -> ℰ T (σ.act i)

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ (σ : Subst Term), 𝒞 Γ σ -> ℰ A t[σ]

notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem ℒ.sound {A t} : ℒ A t -> SN Red t
| .lift _ j => SN.sn (λ _ h => (j h).sound)

theorem ℒ.preservation {A t t'} : ℒ A t -> Red t t' -> ℒ A t'
| .lift _ j, d => j d

theorem ℒ.var A x : ℒ A #x := ℒ.lift (by simp) (λ r => by cases r)

theorem is_lam_rename {r : Ren Term} : {t : Term} -> is_lam t <-> is_lam t⟨r⟩
| .var x => by simp
| .lam A t => by simp
| .app f a => by simp

theorem ℒ.rename {A t} (r : Ren Term) : ℒ A t -> ℒ A t⟨r⟩
| .lift (t := t') j1 j2 =>
  have lem1 (h : is_lam t'⟨r⟩) : ℛ A t'⟨r⟩ := λ k => j1 (is_lam_rename.2 h) (r >> k) |> cast (by simp)
  have lem2 {t''} (d : Red t'⟨r⟩ t'') : ℒ A t'' :=
    have ⟨z, d', e⟩ := d.antirename
    (j2 d').rename r |> cast (by simp [e])
  .lift lem1 lem2

theorem ℛ.lam_mp {A B C b} : ℛ (LR $ A -:> B) (λ[C] b) -> ∀ (r:Ren Term) a, ℰ A a -> ℰ B b[su a::r.to]
| j1, r, a, j2 => j1 r a j2 |> cast (by simp [ℰ])

theorem ℛ.lam_mpr {A B C b} : (∀ (r:Ren Term) a, ℰ A a -> ℰ B b[su a::r.to]) -> ℛ (LR $ A -:> B) (λ[C] b)
| j1, r, a, j2 => j1 r a j2 |> cast (by simp [ℰ])

theorem ℛ.lam {A B C b} : ℛ (LR $ A -:> B) (λ[C] b) <-> ∀ (r:Ren Term) a, ℰ A a -> ℰ B b[su a::r.to] :=
  ⟨lam_mp, lam_mpr⟩

theorem 𝒞.su {Γ A t σ} : ℰ A t -> 𝒞 Γ σ -> 𝒞 (A::Γ) (su t::σ)
| j1, _, 0, _, _ => j1 |> cast (by simp_all)
| _, j2, _ + 1, _, h => j2 h

theorem 𝒞.re {Γ σ} A x : 𝒞 Γ σ -> 𝒞 (A::Γ) (re x::σ)
| _, 0, _, _ => ℒ.var _ x
| j, _ + 1, _, h => j h

theorem 𝒞.rename {Γ} {σ : Subst Term} (r : Ren Term) : 𝒞 Γ σ -> 𝒞 Γ (σ >> r)
| j, i, T, h => ℒ.rename r (j h) |> cast (by simp [ℰ])

theorem 𝒞.weaken {Γ σ} : 𝒞 Γ σ -> 𝒞 Γ (σ >> Ren.succ Term) := rename _

theorem 𝒞.lift A {Γ} {σ : Subst Term} : 𝒞 Γ σ -> 𝒞 (A::Γ) σ.lift
| h, i, T => re A 0 (weaken h) (i := i) (T := T) |> cast (by simp [Subst.rewrite_lift])

theorem ℰ.ind2 {A B s t} {P : Term -> Term -> Prop}
  (ih : ∀ s t,
    ℰ A s ->
    ℰ B t ->
    (∀ s', Red s s' -> P s' t) ->
    (∀ t', Red t t' -> P s t') ->
    P s t)
  : ℰ A s -> ℰ B t -> P s t
:= by
  intro j1 j2
  have j1' := j1
  have j2' := j2
  induction j1 generalizing t; case _ s' q1 q2 qih =>
  induction j2; case _ t' w1 w2 wih =>
  apply ih _ _ j1' j2'
  intro s'' r; apply qih _ j2'; apply ℒ.preservation j1' r; apply j2'; apply r
  intro t'' r; apply wih; apply r; apply ℒ.preservation j2' r

theorem ℰ.lam {A B C b} : SN Red b -> ℛ (LR (A -:> B)) (λ[C] b) -> ℰ (A -:> B) (λ[C] b)
| .sn r, j => .lift (λ _ => j) (λ r' =>
  match r' with
  | .lam (t' := b') r' =>
    have r'' a (k : Ren Term) : Red b[su a :: k.to] b'[su a :: k.to] := Red.subst r'
    ℰ.lam (r _ r') (λ k a ah => ℒ.preservation (j k a ah) (r'' a k |> cast (by simp))))

theorem ℰ.app {A B f a} : ℰ (A -:> B) f -> ℰ A a -> ℰ B (.app f a)
| j1, j2 =>
  ind2 (P := λ f a => ℰ B (.app f a))
    (λ s t j1 j2 ih1 ih2 => ℒ.lift (by simp) (λ r =>
      match r with
      | .beta =>
        match j1 with
        | .lift j1 j3 => ℛ.lam.1 (j1 rfl) 𝐫0 _ j2
      | .app1 r => ih1 _ r
      | .app2 r => ih2 _ r))
    j1 j2

theorem Typing.fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨ t : A
| .var j, σ, h => h j
| .lam (A := A) (B := B) (t := t) tj, σ, h =>
  have norm : SN Red t[σ.lift] := ℒ.sound $ tj.fundamental σ.lift (𝒞.lift A h)
  have body (r : Ren Term) (a : Term) (j : ℰ A a) : ℰ B t[σ.lift >> su a :: r.to] := by
    simp [Subst.rewrite_lift, Subst.compose_compose_left_succ (T := Term)]
    exact tj.fundamental (su a :: (σ >> r)) (𝒞.su j $ 𝒞.rename r h)
  ℰ.lam norm (ℛ.lam.2 $ body |> cast (by simp))
| .app fj aj, σ, h => ℰ.app (fj.fundamental σ h) (aj.fundamental σ h)

theorem Typing.strong_normalization {Γ t A} (j : Γ ⊢ t : A) : SN Red t :=
  have lem : Γ ⊨ t : A := j.fundamental
  have lem : ℰ A t := lem 𝐬0 (λ {i} {T} h => ℒ.var (LR T) i) |> cast (by simp)
  ℒ.sound lem

end STLC
