
import LeanSubst
import Examples.SystemT.Typing

open LeanSubst

namespace SystemT

def SemSet := List Ty -> Ty -> Term -> Prop
def SemRel := List Ty -> Ty -> Term -> Term -> Prop

def Kripke (S : SemSet) : SemSet
| Γ, A, t => ∀ {r Δ}, Γ -⟨r⟩> Δ -> S Δ A t⟨r⟩

mutual
  inductive SnNor : SemSet -> SemSet
  | lam {S1 S2 Γ A B t} :
    Kripke S1 Γ (A -:> B) (λ[A] t) ->
    SnNor S2 (A::Γ) B t ->
    SnNor S1 Γ (A -:> B) (λ[A] t)
  | unit {S Γ} : SnNor S Γ ⊤ `()
  | pair {S1 S2 S3 Γ A B t s} :
    S3 Γ (A `× B) `⟨t, s⟩ ->
    SnNor S1 Γ A t ->
    SnNor S2 Γ B s ->
    SnNor S3 Γ (A `× B) `⟨t, s⟩
  | inj1 {S1 S2 Γ A B t} :
    S2 Γ (A `+ B) (.inj B 1 t) ->
    SnNor S1 Γ A t ->
    SnNor S2 Γ (A `+ B) (.inj B 1 t)
  | inj2 {S1 S2 Γ A B t} :
    S2 Γ (A `+ B) (.inj A 2 t) ->
    SnNor S1 Γ B t ->
    SnNor S2 Γ (A `+ B) (.inj A 2 t)
  | zero {S Γ} : SnNor S Γ ℕ `0
  | succ {S Γ t} : SnNor S Γ ℕ t -> SnNor S Γ ℕ (t `+1)
  | neu {S Γ A t} : SnNeu S Γ A t -> SnNor S Γ A t
  | red {S Γ A t t'} : SnRed S Γ A t t' -> SnNor S Γ A t' -> SnNor S Γ A t

  inductive SnNeu : SemSet -> SemSet
  | var {S Γ A x} : Γ[x]? = .some A -> SnNeu S Γ A #x
  | app {S1 S2 S3 Γ A B f a} : SnNeu S1 Γ (A -:> B) f -> SnNor S2 Γ A a -> SnNeu S3 Γ B (f `• a)
  | proj1 {S1 S2 Γ A B t} : SnNeu S1 Γ (A `× B) t -> SnNeu S2 Γ A (.proj 1 t)
  | proj2 {S1 S2 Γ A B t} : SnNeu S1 Γ (A `× B) t -> SnNeu S2 Γ B (.proj 2 t)
  | absurd {S1 S2 Γ T t} : SnNeu S1 Γ ⊥ t -> SnNeu S2 Γ T (.absurd T t)
  | split {S1 S2 S3 S4 Γ A B C t l r} :
    SnNeu S1 Γ (A `+ B) t ->
    SnNor S2 (A::Γ) C l ->
    SnNor S3 (B::Γ) C r ->
    SnNeu S4 Γ C (.split t l r)
  | nrec {S1 S2 S3 S4 Γ T n z s} :
    SnNeu S1 Γ ℕ n ->
    SnNor S2 Γ T z ->
    SnNor S3 (ℕ::T::Γ) T s ->
    SnNeu S4 Γ T (.nrec n z s)

  inductive SnRed : SemSet -> SemRel
  | beta {S1 S2 Γ A B b t} : SnNor S1 Γ A t -> SnRed S2 Γ B ((λ[A] b) `• t) b[su t .: .id Term]
  | proj1 {S1 S2 Γ A B t s} : SnNor S1 Γ B s -> SnRed S2 Γ A (.proj 1 `⟨t, s⟩) t
  | proj2 {S1 S2 Γ A B t s} : SnNor S1 Γ A t -> SnRed S2 Γ B (.proj 2 `⟨t, s⟩) s
  | split1 {S1 S2 Γ A B C t l r} :
    SnNor S1 Γ A t ->
    SnNor S2 (B::Γ) C r ->
    SnRed S2 Γ C (.split (.inj B 1 t) l r) l[su t .: .id Term]
  | split2 {S1 S2 Γ A B C t l r} :
    SnNor S1 Γ B t ->
    SnNor S2 (A::Γ) C l ->
    SnRed S2 Γ C (.split (.inj A 2 t) l r) r[su t .: .id Term]
  | zero {S1 S2 Γ T z s} : SnNor S1 (ℕ::T::Γ) T s -> SnRed S2 Γ T (.nrec `0 z s) z
  | succ {S1 S2 S3 Γ T n z s} :
    SnNor S1 Γ ℕ n ->
    SnNor S2 Γ T (.nrec n z s) ->
    SnRed S3 Γ T (.nrec (n `+1) z s) s[su n .: su (.nrec n z s) .: .id Term]
  | step_app {S1 S2 Γ A B f a f'} : SnRed S1 Γ (A -:> B) f f' -> SnRed S2 Γ B (f `• a) (f' `• a)
  | step_proj1 {S1 S2 Γ A B t t'} :
    SnRed S1 Γ (A `× B) t t' ->
    SnRed S2 Γ A (.proj 1 t) (.proj 1 t')
  | step_proj2 {S1 S2 Γ A B t t'} :
    SnRed S1 Γ (A `× B) t t' ->
    SnRed S2 Γ B (.proj 2 t) (.proj 2 t')
  | step_absurd {S1 S2 Γ T t t'} : SnRed S1 Γ ⊥ t t' -> SnRed S2 Γ T (.absurd T t) (.absurd T t')
  | step_split {S1 S2 Γ A B C t l r t'} :
    SnRed S1 Γ (A `+ B) t t' ->
    SnRed S2 Γ C (.split t l r) (.split t' l r)
  | step_nrec {S1 S2 Γ T n z s n'} : SnRed S1 Γ ℕ n n' -> SnRed S2 Γ T (.nrec n z s) (.nrec n' z s)
end

-- This is probably needed somewhere?
-- mutual
--   theorem SnNor.rename {S t} (r : Ren Term) : SnNor S t -> SnNor S t⟨r⟩ := sorry

--   theorem SnNeu.rename {S t} (r : Ren Term) : SnNeu S t -> SnNeu S t⟨r⟩ := sorry

--   theorem SnRed.rename {S t t'} (r : Ren Term) : SnRed S t t' -> SnRed S t⟨r⟩ t'⟨r⟩ := sorry
-- end

@[simp]
def 𝒱 : Ty -> SemSet
| A -:> B, Γ, _, λ[_] t => ∀ {a}, SnNor (𝒱 A) Γ A a -> SnNor (𝒱 B) Γ B t[su a .: .id Term]
| A `+ _, Γ, _, .inj _ 1 t => SnNor (𝒱 A) Γ A t
| _ `+ B, Γ, _, .inj _ 2 t => SnNor (𝒱 B) Γ B t
| A `× B, Γ, _, `⟨a, b⟩ => SnNor (𝒱 A) Γ A a ∧ SnNor (𝒱 B) Γ B b
| _, _, _, _ => False

def ℰ Γ A := SnNor (𝒱 A) Γ A

structure SemSubst (Γ : List Ty) (Δ : List Ty) (σ : Subst Term) where
  act : ∀ {i T}, Γ[i]? = .some T -> ℰ Δ T (σ.act i)

notation:35 Γ:35 " -⟦" σ "⟧> " Δ:35 => SemSubst Γ Δ σ

@[simp]
def SemTyping (Γ : List Ty) (t : Term) (A : Ty) := ∀ {σ Δ}, SemSubst Γ Δ σ -> ℰ Δ A t[σ]

notation:60 Γ:60 " ⊨ " t:60 " : " A:60 => SemTyping Γ t A

theorem SemSubst.id {Γ} : Γ -⟦.id Term⟧> Γ := sorry

theorem SemSubst.su {Γ Δ A σ a} (j : ℰ Δ A a) (m : Γ -⟦σ⟧> Δ) : (A::Γ) -⟦su a .: σ⟧> Δ :=
  ⟨λ {i T} h =>
    match i with
    | 0 =>
      have e : A = T := h %simp
      j %simp [e]
    | i + 1 => m.act h⟩

theorem SemSubst.lift {Γ Δ σ} (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := sorry

theorem SemSubst.comp {Γ Δ Ξ σ r} (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> Ξ) : Γ -⟦σ >> ·⟨r⟩⟧> Ξ := sorry

theorem ℰ.app {S Δ T A B f a}
  (e1 : S = 𝒱 (A -:> B)) (e2 : T = A -:> B)
  (j1 : ℰ Δ A a)
  : SnNor S Δ T f -> ℰ Δ B (f `• a)
| .lam (A := A') (B := B') (t := t) j3 j4 =>
  have e3 : A = A' ∧ B = B' := by injection e2; simp [*]
  have j3' : ∀ {a}, SnNor (𝒱 A) Δ A a -> SnNor (𝒱 B) Δ B t[su a .: .id Term] := by
    simp_all [Kripke]; exact (j3 .id)
  .red (.beta (S1 := 𝒱 A') $ j1 %simp [e3.1, ℰ]) (j3' j1)
| .neu j3 => sorry
| .red j3 j4 => sorry

theorem ℰ.fst {S Δ T A B t}
  (e1 : S = 𝒱 (A `× B)) (e2 : T = (A `× B))
  : SnNor S Δ T t -> ℰ Δ A t.!1
| .pair (A := A') (B := B') (t := t) (s := s) j3 j4 j5 =>
  have e3 : A = A' ∧ B = B' := by injection e2; simp [*]
  have j3' : ℰ Δ A t ∧ ℰ Δ B s := j3 %simp [e1, ℰ]
  .red (.proj1 j3'.2) j3'.1
| .neu j3 => sorry
| .red j3 j4 => sorry

theorem ℰ.snd {S Δ T A B t}
  (e1 : S = 𝒱 (A `× B)) (e2 : T = (A `× B))
  : SnNor S Δ T t -> ℰ Δ B t.!2
| .pair (A := A') (B := B') (t := t) (s := s) j3 j4 j5 =>
  have e3 : A = A' ∧ B = B' := by injection e2; simp [*]
  have j3' : ℰ Δ A t ∧ ℰ Δ B s := j3 %simp [e1, ℰ]
  .red (.proj2 j3'.1) j3'.2
| .neu j3 => sorry
| .red j3 j4 => sorry

theorem ℰ.absurd {S Δ T A t}
  (e1 : S = 𝒱 ⊥) (e2 : T = ⊥)
  : SnNor S Δ T t -> ℰ Δ A (.absurd A t)
| .lam j3 j4 => by injection e2
| .neu j3 => .neu $ .absurd (S1 := S) $ j3 %simp [e2]
| .red j3 j4 => .red (.step_absurd (S1 := S) $ j3 %simp [e1, e2]) (ℰ.absurd e1 e2 j4)

theorem ℰ.split {S Δ T A B C t l r}
  (e1 : S = 𝒱 (A `+ B)) (e2 : T = (A `+ B))
  (j1 : ℰ (A::Δ) C l) (j2 : ℰ (B::Δ) C r)
  (j1' : ∀ {x}, ℰ Δ A x -> ℰ Δ C l[su x .: .id Term])
  (j2' : ∀ {x}, ℰ Δ B x -> ℰ Δ C r[su x .: .id Term])
  : SnNor S Δ T t -> ℰ Δ C (.split t l r)
| .inj1 (A := A') (B := B') (t := t) j3 j4 =>
  have e3 : A = A' ∧ B = B' := by injection e2; simp [*]
  have j3' : ℰ Δ A t := j3 %simp [e1, ℰ]
  .red (.split1 j4 (j2 %simp [e1, e3, ℰ])) (j1' j3')
| .inj2 j3 j4 => sorry
| .neu j3 => sorry
| .red j3 j4 => sorry

theorem ℰ.nrec {S Δ A T n z s}
  (e1 : S = 𝒱 ℕ) (e2 : T = ℕ)
  (j1 : ℰ Δ A z) (j2 : ℰ (ℕ::A::Δ) A s)
  (j2' : ∀ {x y}, ℰ Δ ℕ x -> ℰ Δ A y -> ℰ Δ A s[su x .: su y .: .id Term])
  : SnNor S Δ T n -> ℰ Δ A (.nrec n z s)
| .lam j3 j4 => by injection e2
| .zero => .red (.zero j2) j1
| .succ j3 =>
  have ih := nrec e1 e2 j1 j2 j2' j3
  .red (.succ j3 ih) (j2' (j3 %simp [e1, ℰ]) ih)
| .neu j3 => .neu $ .nrec (S1 := S) (j3 %simp [e2]) j1 j2
| .red (t' := n') j3 j4 =>
  .red (.step_nrec (S1 := S) (j3 %simp [e2])) (ℰ.nrec e1 e2 j1 j2 j2' j4)

section
set_option quotPrecheck false in
set_option hygiene false in
local notation "⟦" t "⟧" => Typing.fundamental t

theorem Typing.fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨ t : A
| var x, σ, Δ, mσ => mσ.act x
| lam (A := A') (B := B) (t := t) tj, σ, Δ, mσ =>
  have lem : Kripke (𝒱 (A' -:> B)) Δ (A' -:> B) (λ[A'] t)[σ] := λ {r Ξ} mr {a} aj =>
    have tj' := ⟦tj⟧ (.su aj $ mσ.comp mr)
    by simp; norm_subst; exact tj'
  .lam lem (⟦tj⟧ $ mσ.lift A')
| app f a, σ, Δ, mσ => ℰ.app rfl rfl (⟦a⟧ mσ) (⟦f⟧ mσ)
| unit, σ, Δ, mσ => .unit
| pair t s, σ, Δ, mσ => .pair ⟨⟦t⟧ mσ, ⟦s⟧ mσ⟩ (⟦t⟧ mσ) (⟦s⟧ mσ)
| fst t, σ, Δ, mσ => ℰ.fst rfl rfl (⟦t⟧ mσ)
| snd t, σ, Δ, mσ => ℰ.snd rfl rfl (⟦t⟧ mσ)
| absurd t, σ, Δ, mσ => ℰ.absurd rfl rfl (⟦t⟧ mσ)
| split (A := A') (B := B) (l := l) (r := r) t lj rj, σ, Δ, mσ =>
  have lem1 {x} {jx : ℰ Δ A' x} : ℰ Δ A l[σ.lift][su x .: .id Term] := (⟦lj⟧ $ mσ.su jx) %simp
  have lem2 {x} {jx : ℰ Δ B x}  : ℰ Δ A r[σ.lift][su x .: .id Term] := (⟦rj⟧ $ mσ.su jx) %simp
  ℰ.split rfl rfl (⟦lj⟧ $ mσ.lift A') (⟦rj⟧ $ mσ.lift B) (λ {x} => @lem1 x) (λ {x} => @lem2 x) (⟦t⟧ mσ)
| inj1 t, σ, Δ, mσ => .inj1 (⟦t⟧ mσ) (⟦t⟧ mσ)
| inj2 t, σ, Δ, mσ => .inj2 (⟦t⟧ mσ) (⟦t⟧ mσ)
| zero, σ, Δ, mσ => .zero
| succ t, σ, Δ, mσ => .succ (⟦t⟧ mσ)
| nrec (s := s) n z sj, σ, Δ, mσ =>
  have lem {x y} (jx : ℰ Δ ℕ x) (jy : ℰ Δ A y) : ℰ Δ A s[σ.lift [] 2][su x .: su y .: .id Term] :=
    (⟦sj⟧ $ (mσ.su jy).su jx) %simp
  ℰ.nrec rfl rfl (⟦z⟧ mσ) (⟦sj⟧ $ (mσ.lift A).lift ℕ %simp) lem (⟦n⟧ mσ)
end

notation "⟦" t "⟧" => Typing.fundamental t

mutual
  -- Note: Lean is smart enough to exclude the lam case if we additionally match on `e2`, but the
  -- performance is not great. Amusingly, if we include *only* the lam case, it excludes the rest
  -- without performance problems
  theorem SnNor.consistency {S Γ T t} (e1 : Γ = []) (e2 : T = ⊥) : ¬ SnNor S Γ T t
  | .lam j1 j2 => by injection e2
  | .neu j1 => j1.consistency e1
  | .red j1 j2 => j2.consistency e1 e2

  theorem SnNeu.consistency {S Γ T t} (e : Γ = []) : ¬ SnNeu S Γ T t
  | .var h => by simp_all
  | .app j _ | .proj1 j | .proj2 j | .absurd j | .split j _ _ | .nrec j _ _ =>
    j.consistency e
end

theorem Typing.consistency {t} : ¬ ([] ⊢ t : ⊥) := λ j => SnNor.consistency rfl rfl (⟦j⟧ .id)

end SystemT
