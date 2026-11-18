
import Examples.SystemFWithData.Term
open LeanSubst

namespace SystemFWithData

section
set_option quotPrecheck false in
set_option hygiene false in
local notation:60 Γ:60 " ⊢ " t:60 " : " A:60 => Typing Γ t A

inductive Typing : List Ty -> Term -> Ty -> Prop where
| var {Γ x A} :
  Γ[x]? = some A ->
  Γ ⊢ #x : A
| app {Γ A B f a} :
  Γ ⊢ f : A -:> B ->
  Γ ⊢ a : A ->
  Γ ⊢ f `• a : B
| lam {Γ A B t} :
  A::Γ ⊢ t : B ->
  Γ ⊢ λ[A] t : A -:> B
| tapp {Γ P P' A f} :
  Γ ⊢ f : `∀ P ->
  P' = P[su A.:𝐬0] ->
  Γ ⊢ f •[A] : P'
| tlam {Γ P t} :
  Γ⟨.add Ty 1⟩ ⊢ t : P ->
  Γ ⊢ Λ t : `∀ P
end

notation:200 Γ:200 " ⊢ " t:200 " : " A:200 => Typing Γ t A

-- inductive ListWf : List Unit -> List Ty -> Prop where
-- | nil {Δ} : ListWf Δ []
-- | cons {Δ Γ A} : Δ ⊢ A type -> ListWf Δ Γ -> ListWf Δ (A::Γ)

-- theorem ListWf.get {Δ Γ T} {x : Nat} (wf : ListWf Δ Γ) (h : Γ[x]? = some T) : Δ ⊢ T type :=
--   match wf, x with
--   | .nil, _ => by cases h
--   | .cons (A := A) j wf, 0 =>
--     have e : A = T := by simp at h; exact h
--     j %simp [e]
--   | .cons j wf, x + 1 => wf.get h

-- structure KindingRen (r : Ren Ty) (Δ Δ' : List Unit) where
--   act : ∀ {x T}, Δ[x]? = some T -> Δ'[r.act x]? = some T

-- theorem KindingRen.id Δ : KindingRen (.id Ty) Δ Δ := ⟨λ j => j⟩

-- theorem KindingRen.succ Δ : KindingRen (.add Ty 1) Δ (()::Δ) := ⟨λ h => h⟩

-- theorem KindingRen.lift {Δ Δ' : List Unit} {r : Ren Ty} (h : KindingRen r Δ Δ')
--   : KindingRen r.lift (.unit::Δ) (.unit::Δ')
-- := ⟨λ {x} _ j =>
--     match x with
--     | 0 => j %simp
--     | _ + 1 => h.act j⟩

-- theorem Kinding.rename {Δ Δ' A} {r : Ren Ty} (m : KindingRen r Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A⟨r⟩ type
-- | var j => var (m.act j)
-- | nat => nat
-- | arrow j1 j2 => arrow (j1.rename m) (j2.rename m)
-- | all j => all (j.rename $ m.lift)

-- structure KindingSubst (σ : Subst Ty) (Δ Δ' : List Unit) where
--   act : ∀ {x : Nat} {T}, Δ[x]? = some T -> Δ' ⊢ σ.act x type

-- theorem KindingSubst.id Δ : KindingSubst (.id Ty) Δ Δ := ⟨λ j => .var j⟩

-- theorem KindingSubst.cons {Δ Δ' τ A} (j : Δ' ⊢ A type) (mτ : KindingSubst τ Δ Δ')
--   : KindingSubst (su A .: τ) (() :: Δ) Δ'
-- := ⟨λ {x T} h =>
--     match x with
--     | 0 => by simp [j]
--     | _ + 1 => by simp_all; exact mτ.act h⟩

-- theorem KindingSubst.lift {Δ Δ' : List Unit} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
--   : KindingSubst (σ.lift []) (.unit::Δ) (.unit::Δ')
-- := ⟨λ {x} _ j =>
--     match x with
--     | 0 => .var j %simp
--     | _ + 1 => ((m.act j).rename $ .succ Δ') %simp ⟩

-- theorem Kinding.subst {Δ Δ' A} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
--   : Δ ⊢ A type -> Δ' ⊢ A[σ] type
-- | var j => m.act j
-- | nat => nat
-- | arrow j1 j2 => arrow (j1.subst m) (j2.subst m)
-- | all j => all (j.subst $ m.lift)

-- theorem Kinding.beta {Δ A B} (j1 : Δ ⊢ B type) (j2 : (()::Δ) ⊢ A type) : Δ ⊢ A[su B .: 𝐬0] type :=
--   j2.subst $ KindingSubst.cons j1 (.id Δ)

structure TypingRen (r : Ren Term) (Γ Γ' : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Γ'[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.id Γ : TypingRen (.id Term) Γ Γ := ⟨λ j => j⟩

theorem TypingRen.add Γ A : TypingRen (.add Term A.length) Γ (A ++ Γ) :=
  ⟨λ j => by simp; rw [List.getElem?_append_right (by lia)]; simp [j]⟩

theorem TypingRen.lift {Γ Γ' r} (m : TypingRen r Γ Γ') (A : List Ty)
  : TypingRen (r.lift A.length) (A ++ Γ) (A ++ Γ')
:= ⟨λ {x} _ j =>
    match x.decLt A.length with
    | isTrue h =>
      j %simp [-Ren.lift, Ren.lift_act_lt h, List.getElem?_append_left h]
    | isFalse h => by
      replace h : x ≥ A.length := by lia
      rw [Ren.lift_act_ge h]
      rw [List.getElem?_append_right (by lia)] at *; simp
      exact m.act j⟩

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem := congrArg (λ x => x⟨.sub Ty k⟩) h
  have act := @act x T⟨.sub Ty k⟩ $ lem %simp
  by norm_subst [act, <-h]⟩

theorem Typing.rename {Γ Γ' A t} {r2 : Ren Term}
  (r1 : Ren Ty) (m2 : TypingRen r2 Γ Γ')
  : Γ ⊢ t : A -> Γ'⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
| var (x := x) j1 => sorry
  -- have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
  -- var (j1 %simp) (j2.rename m1)
| app j1 j2 => app (j1.rename r1 m2) (j2.rename r1 m2)
| lam (A := A) j1 => lam (j1.rename r1 $ m2.lift [A])
| tapp j1 e => tapp (j1.rename r1 m2) (by simp [e])
| tlam j => tlam (j.rename r1.lift (m2.shift 1) %simp)

structure TypingSubst (σ : Subst Term) (τ : Subst Ty) (Γ Γ' : List Ty) where
  act : ∀ {x} {T : Ty}, Γ[x]? = some T -> Γ'[τ] ⊢ σ.act x : T[τ]


notation:35 Γ:35 " -[" σ "," τ "]> " Δ:35 => TypingSubst σ τ Γ Δ

theorem TypingSubst.lift {σ τ Γ Γ' A}
  (m : TypingSubst σ τ Γ Γ')
  : TypingSubst (σ.lift [Ty] A.length) τ (A ++ Γ) (A ++ Γ')
:= ⟨λ {x T} j => sorry⟩
  -- match x.decLt A.length with
  -- | isTrue h =>
  --   have lem1 := List.getElem?_append_left h ▸ j
  --   have lem2 : x < A[τ].length := by simp [h]
  --   have j' : (A[τ] ++ Γ'[τ]) ⊢ .var x : T[τ] := .var
  --     (by simp [List.getElem?_append_left lem2]; norm_subst [lem1])
  --     (.subst m.ty $ wf.get lem1)
  --   j' %simp [-Subst.lift, Subst.lift_act_lt h]
  -- | isFalse h =>
  --   have h : x ≥ A.length := by lia
  --   have lem1 := List.getElem?_append_right h ▸ j
  --   have lem2 := (m.act lem1).rename (.id Δ') (.add Γ'[τ] A[τ])
  --   lem2 %simp [-Subst.lift, Subst.lift_act_ge h]⟩

-- theorem TypingSubst.lift_ty {σ τ Δ Δ' Γ Γ'} (m : TypingSubst σ τ Δ Δ' Γ Γ')
--   : TypingSubst (σ >> RenVec.add [Term, Ty] [0, 1]) (τ.lift)
--     (() :: Δ) (() :: Δ')
--     Γ⟨.add Ty 1⟩ Γ'⟨.add Ty 1⟩
-- := ⟨.lift m.ty, λ {x T} j =>
--   have ⟨_, h⟩ := List.getElem?_eq_some_iff.1 j
--   have lem1 := congrArg (λ x => x⟨.sub Ty 1⟩) j
--   have lem2 := @m.act x T⟨.sub Ty 1⟩ $ lem1 %simp
--   lem2.rename (.succ Δ') (.id Γ'[τ]) %simp [<-h] ⟩

-- theorem Typing.kinded {Δ Γ t A} : Δ&Γ ⊢ t : A -> Δ ⊢ A type
-- | var j1 j2 => j2
-- | app j1 j2 =>
--   match j1.kinded with
--   | .arrow j1' j3 => j3
-- | lam j1 j2 => Kinding.arrow j1 j2.kinded
-- | tapp j1 j2 e =>
--   match j1.kinded with
--   | .all j1' => Kinding.beta j2 j1' |> cast (by simp [e])
-- | tlam j => Kinding.all j.kinded
-- | zero => Kinding.nat
-- | succ j => j.kinded
-- | nrec j1 j2 j3 => j1.kinded

theorem Typing.subst {Γ Γ' A t} {σ : Subst Term} {τ : Subst Ty}
  (mσ : TypingSubst σ τ Γ Γ')
  : Γ ⊢ t : A -> Γ'[τ] ⊢ t[σ, τ] : A[τ]
| var (x := x) j => mσ.act j
| app j1 j2 => app (j1.subst mσ) (j2.subst mσ)
| lam (A := A) j => sorry --lam (j.subst (mσ.lift (.cons j1 .nil)) %simp)
| tapp j e => tapp (j.subst mσ) (by simp [e])
| tlam j => sorry --tlam (j.subst (mσ.lift_ty) %simp )

end SystemFWithData
