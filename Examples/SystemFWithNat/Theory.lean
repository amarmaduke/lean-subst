
import Examples.SystemFWithNat.Term
open LeanSubst

namespace SystemFWithNat

inductive Kinding : List Unit -> Ty -> Prop where
| var {Δ x} :
  Δ[x]? = some .unit ->
  Kinding Δ (.var x)
| nat {Δ} :
  Kinding Δ .nat
| arrow {Δ A B} :
  Kinding Δ A ->
  Kinding Δ B ->
  Kinding Δ (.arrow A B)
| all {Δ P} :
  Kinding (.unit::Δ) P ->
  Kinding Δ (.all P)

notation:170 Δ:170 " ⊢ " A:170 " type" => Kinding Δ A

inductive Typing  : List Unit -> List Ty -> Term -> Ty -> Prop where
| var {Δ Γ x A} :
  Γ[x]? = some A ->
  Δ ⊢ A type ->
  Typing Δ Γ (.var x) A
| app {Δ Γ A B f a} :
  Typing Δ Γ f (.arrow A B) ->
  Typing Δ Γ a A ->
  Typing Δ Γ (.app f a) B
| lam {Δ Γ A B t} :
  Δ ⊢ A type ->
  Typing Δ (A::Γ) t B ->
  Typing Δ Γ (.lam A t) (.arrow A B)
| tapp {Δ Γ P P' A f} :
  Typing Δ Γ f (.all P) ->
  Δ ⊢ A type ->
  P' = P[su A.:𝐬0] ->
  Typing Δ Γ (.tapp f A) P'
| tlam {Δ Γ P t} :
  Typing (.unit::Δ) Γ⟨.add Ty 1⟩ t P ->
  Typing Δ Γ (.tlam t) (.all P)
| zero {Δ Γ} :
  Typing Δ Γ .zero .nat
| succ {Δ Γ n} :
  Typing Δ Γ n .nat ->
  Typing Δ Γ (.succ n) .nat
| nrec {Δ Γ A z s n} :
  Typing Δ Γ z A ->
  Typing Δ (A::.nat::Γ) s A ->
  Typing Δ Γ n .nat ->
  Typing Δ Γ (.nrec z s n) A

notation:200 Δ:200 "&" Γ:200 " ⊢ " t:200 " : " A:200 => Typing Δ Γ t A

structure KindingRen (r : Ren Ty) (Δ Δ' : List Unit) where
  act : ∀ {x T}, Δ[x]? = some T -> Δ'[r.act x]? = some T

theorem KindingRen.id Δ : KindingRen (.id Ty) Δ Δ := ⟨λ j => j⟩

theorem KindingRen.succ {A X} : KindingRen (.add Ty 1) X (A::X) := ⟨λ h => h⟩

theorem KindingRen.lift {Δ Δ' : List Unit} {r : Ren Ty} (h : KindingRen r Δ Δ')
  : KindingRen r.lift (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => lsimp j
    | _ + 1 => lsimp h.act j⟩

theorem Kinding.rename {Δ Δ' A} {r : Ren Ty} (m : KindingRen r Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A⟨r⟩ type
| var j => var (m.act j)
| nat => nat
| arrow j1 j2 => arrow (j1.rename m) (j2.rename m)
| all j => all (j.rename $ m.lift)

structure KindingSubst (σ : Subst Ty) (Δ Δ' : List Unit) where
  act : ∀ {x : Nat} {T}, Δ[x]? = some T -> Δ' ⊢ σ.act x type

theorem KindingSubst.lift {Δ Δ' : List Unit} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
  : KindingSubst (σ.lift []) (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => lsimp .var j
    | _ + 1 => lsimp (m.act j).rename (Δ' := .unit::Δ') KindingRen.succ⟩

theorem Kinding.subst {Δ Δ' A} {σ : Subst Ty} (m : KindingSubst σ Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A[σ] type
| var j => m.act j
| nat => nat
| arrow j1 j2 => arrow (j1.subst m) (j2.subst m)
| all j => all (j.subst $ m.lift)

structure TypingRen (r : Ren Term) (Γ Γ' : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Γ'[r.act x]? = some T

theorem TypingRen.add Γ A : TypingRen (.add Term A.length) Γ (A ++ Γ) :=
  ⟨λ j => by simp; rw [List.getElem?_append_right (by lia)]; simp [j]⟩

theorem TypingRen.lift {Γ Γ' r} (m : TypingRen r Γ Γ') (A : List Ty)
  : TypingRen (r.lift A.length) (A ++ Γ) (A ++ Γ')
:= ⟨λ {x} _ j =>
    match x.decLt A.length with
    | isTrue h => by
      rw [Ren.lift_act_lt h]
      rw [List.getElem?_append_left h] at *
      exact j
    | isFalse h => by
      replace h : x ≥ A.length := by lia
      rw [Ren.lift_act_ge h]
      rw [List.getElem?_append_right (by lia)] at *; simp
      exact m.act j⟩

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem : Γ⟨.add Ty k⟩[x]?⟨.sub Ty k⟩ = some T⟨.sub Ty k⟩ := by simp [h]
  by {
    simp at lem; replace act := act lem
    rw [<-List.rmap_get?, act]
    rw [<-Option.rmap_some, <-h]
    simp
  }⟩

theorem Typing.rename {Δ Δ' Γ Γ' A t} {r1 : Ren Ty} {r2 : Ren Term}
  (m1 : KindingRen r1 Δ Δ') (m2 : TypingRen r2 Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
| var (x := x) j1 j2 =>
  have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
  var (lsimp j1) (j2.rename m1)
| app j1 j2 => app (j1.rename m1 m2) (j2.rename m1 m2)
| lam (A := A) j1 j2 => lam (j1.rename m1) (j2.rename m1 $ m2.lift [A])
| tapp j1 j2 e => tapp (j1.rename m1 m2) (j2.rename m1) (by simp [e])
| tlam j => tlam (lsimp j.rename m1.lift (m2.shift 1))
| zero => zero
| succ j => succ (j.rename m1 m2)
| nrec j1 j2 j3 => nrec (j1.rename m1 m2) (j2.rename m1 $ m2.lift [A, Ty.nat]) (j3.rename m1 m2)

structure TypingSubst (σ : Subst Term) Δ (Γ Γ' : List Ty) where
  act : ∀ {x} {T : Ty}, Γ[x]? = some T -> Δ&Γ' ⊢ σ.act x : T

theorem TypingSubst.lift {Δ Γ Γ' σ} (m : TypingSubst σ Δ Γ Γ') (A : List Ty)
  : TypingSubst (σ.lift [Ty] A.length) Δ (A ++ Γ) (A ++ Γ')
:= ⟨λ {x T} j =>
    match x.decLt A.length with
    | isTrue h => by
      sorry
      -- rw [Subst.lift_act_lt h]
      -- apply Typing.var; simp
      -- have lem : x < A[τ].length := by simp [h]
      -- rw [List.getElem?_append_left (by simp [h])] at *
      -- rw [<-List.smap_get?, j1]; simp
      -- apply Kinding.subst j2 j3
    | isFalse h => by
      sorry
      -- replace h : x ≥ A.length := by lia
      -- rw [Subst.lift_act_ge h]
      -- rw [List.getElem?_append_right (by lia)] at j1
      -- have lem1 := m.act j1 j2 j3
      -- have lem2 := Typing.rename (KindingRen.id Δ') (TypingRen.add Γ'[τ] A[τ]) lem1
      -- simp_all
    ⟩

theorem TypingSubst.shift {Δ Γ Γ' σ} A
  : TypingSubst σ Δ Γ Γ' ->
    TypingSubst (σ >> RenVec.add [Term, Ty] [0, 1])
      (A ++ Δ) Γ⟨.add Ty A.length⟩ Γ'⟨.add Ty A.length⟩
| ⟨act⟩ => ⟨λ {x T} j => by

  -- have lem : Γ⟨.add Ty k⟩[x]?⟨.sub Ty k⟩ = some T⟨.sub Ty k⟩ := by simp [h]
  -- by {
  --   simp at lem; replace act := act lem
  --   rw [<-List.rmap_get?, act]
  --   rw [<-Option.rmap_some, <-h]
  --   simp
    --have lem : Γ⟨.add Ty A.length⟩[x]?⟨.sub Ty A.length⟩ = some T⟨.sub Ty A.length⟩ := by simp [j1]
    --simp at lem
    sorry
  ⟩

theorem Typing.subst_ty {Δ Δ' Γ A t} {σ : Subst Ty} (mσ : KindingSubst σ Δ Δ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ[σ] ⊢ t[.id Term, σ] : A[σ]
| var (x := x) j1 j2 => var (by rw [<-List.smap_get?, j1]; simp) (j2.subst mσ)
| app j1 j2 => app (j1.subst_ty mσ) (j2.subst_ty mσ)
| lam (A := A) j1 j2 => lam (j1.subst mσ) (lsimp j2.subst_ty mσ)
| tapp j1 j2 e => tapp (j1.subst_ty mσ) (j2.subst mσ) (by simp [e])
| tlam j => tlam (by simp; sorry) --tlam (lsimp j.subst_ty mσ.lift (mτ.shift [()]))
| zero => zero
| succ j => succ (j.subst_ty mσ)
| nrec j1 j2 j3 => nrec (j1.subst_ty mσ) (lsimp j2.subst_ty mσ) (j3.subst_ty mσ)

theorem Typing.subst {Δ Δ' Γ Γ' A t} {σ : Subst Ty} {τ : Subst Term}
  (mσ : KindingSubst σ Δ Δ') (mτ : TypingSubst τ Δ Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'[σ] ⊢ t[τ, σ] : A[σ]
| var (x := x) j1 j2 => by
  have lem := subst_ty mσ $ mτ.act j1
  simp; simp at lem
  sorry
| app j1 j2 => app (j1.subst mσ mτ) (j2.subst mσ mτ)
| lam (A := A) j1 j2 => lam (j1.subst mσ) (lsimp j2.subst mσ $ mτ.lift [A])
| tapp j1 j2 e => tapp (j1.subst mσ mτ) (j2.subst mσ) (by simp [e])
| tlam j => tlam (lsimp j.subst mσ.lift (mτ.shift [()]))
| zero => zero
| succ j => succ (j.subst mσ mτ)
| nrec j1 j2 j3 => nrec (j1.subst mσ mτ) (lsimp j2.subst mσ $ mτ.lift [A, Ty.nat]) (j3.subst mσ mτ)

end SystemFWithNat
