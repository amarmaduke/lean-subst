
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

inductive Typing : List Unit -> List Ty -> Term -> Ty -> Prop where
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

inductive ListWf : List Unit -> List Ty -> Prop where
| nil {Δ} : ListWf Δ []
| cons {Δ Γ A} : Δ ⊢ A type -> ListWf Δ Γ -> ListWf Δ (A::Γ)

theorem ListWf.get {Δ Γ T} {x : Nat} (wf : ListWf Δ Γ) (h : Γ[x]? = some T) : Δ ⊢ T type :=
  match wf, x with
  | .nil, _ => by cases h
  | .cons (A := A) j wf, 0 =>
    have e : A = T := by simp at h; exact h
    simp% [e] j
  | .cons j wf, x + 1 => wf.get h

structure KindingRen (r : Ren Ty) (Δ Δ' : List Unit) where
  act : ∀ {x T}, Δ[x]? = some T -> Δ'[r.act x]? = some T

theorem KindingRen.id Δ : KindingRen (.id Ty) Δ Δ := ⟨λ j => j⟩

theorem KindingRen.succ Δ : KindingRen (.add Ty 1) Δ (()::Δ) := ⟨λ h => h⟩

theorem KindingRen.lift {Δ Δ' : List Unit} {r : Ren Ty} (h : KindingRen r Δ Δ')
  : KindingRen r.lift (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => simp% j
    | _ + 1 => simp% h.act j⟩

theorem Kinding.rename {Δ Δ' A} {r : Ren Ty} (m : KindingRen r Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A⟨r⟩ type
| var j => var (m.act j)
| nat => nat
| arrow j1 j2 => arrow (j1.rename m) (j2.rename m)
| all j => all (j.rename $ m.lift)

structure KindingSubst (σ : Subst Ty) (Δ Δ' : List Unit) where
  act : ∀ {x : Nat} {T}, Δ[x]? = some T -> Δ' ⊢ σ.act x type

theorem KindingSubst.id Δ : KindingSubst (.id Ty) Δ Δ := ⟨λ j => .var j⟩

theorem KindingSubst.cons {Δ Δ' τ A} (j : Δ' ⊢ A type) (mτ : KindingSubst τ Δ Δ')
  : KindingSubst (su A .: τ) (() :: Δ) Δ'
:= ⟨λ {x T} h =>
    match x with
    | 0 => by simp [j]
    | _ + 1 => by simp_all; exact mτ.act h⟩

theorem KindingSubst.lift {Δ Δ' : List Unit} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
  : KindingSubst (σ.lift []) (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => simp% .var j
    | _ + 1 => simp% (m.act j).rename $ .succ Δ'⟩

theorem Kinding.subst {Δ Δ' A} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
  : Δ ⊢ A type -> Δ' ⊢ A[σ] type
| var j => m.act j
| nat => nat
| arrow j1 j2 => arrow (j1.subst m) (j2.subst m)
| all j => all (j.subst $ m.lift)

theorem Kinding.beta {Δ A B} (j1 : Δ ⊢ B type) (j2 : (()::Δ) ⊢ A type) : Δ ⊢ A[su B .: 𝐬0] type :=
  j2.subst $ KindingSubst.cons j1 (.id Δ)

structure TypingRen (r : Ren Term) (Γ Γ' : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Γ'[r.act x]? = some T

theorem TypingRen.id Γ : TypingRen (.id Term) Γ Γ := ⟨λ j => j⟩

theorem TypingRen.add Γ A : TypingRen (.add Term A.length) Γ (A ++ Γ) :=
  ⟨λ j => by simp; rw [List.getElem?_append_right (by lia)]; simp [j]⟩

theorem TypingRen.lift {Γ Γ' r} (m : TypingRen r Γ Γ') (A : List Ty)
  : TypingRen (r.lift A.length) (A ++ Γ) (A ++ Γ')
:= ⟨λ {x} _ j =>
    match x.decLt A.length with
    | isTrue h =>
      simp% [-Ren.lift, Ren.lift_act_lt h, List.getElem?_append_left h] j
    | isFalse h => by
      replace h : x ≥ A.length := by lia
      rw [Ren.lift_act_ge h]
      rw [List.getElem?_append_right (by lia)] at *; simp
      exact m.act j⟩

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem := congrArg (λ x => x⟨.sub Ty k⟩) h
  have act := @act x T⟨.sub Ty k⟩ $ simp% lem
  by norm_subst [act, <-h]⟩

theorem Typing.rename {Δ Δ' Γ Γ' A t} {r1 : Ren Ty} {r2 : Ren Term}
  (m1 : KindingRen r1 Δ Δ') (m2 : TypingRen r2 Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
| var (x := x) j1 j2 =>
  have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
  var (simp% j1) (j2.rename m1)
| app j1 j2 => app (j1.rename m1 m2) (j2.rename m1 m2)
| lam (A := A) j1 j2 => lam (j1.rename m1) (j2.rename m1 $ m2.lift [A])
| tapp j1 j2 e => tapp (j1.rename m1 m2) (j2.rename m1) (by simp [e])
| tlam j => tlam (simp% j.rename m1.lift (m2.shift 1))
| zero => zero
| succ j => succ (j.rename m1 m2)
| nrec j1 j2 j3 => nrec (j1.rename m1 m2) (j2.rename m1 $ m2.lift [A, Ty.nat]) (j3.rename m1 m2)

structure TypingSubst (σ : Subst Term) (τ : Subst Ty) (Δ Δ' : List Unit) (Γ Γ' : List Ty) where
  ty : KindingSubst τ Δ Δ'
  act : ∀ {x} {T : Ty}, Γ[x]? = some T -> Δ'&Γ'[τ] ⊢ σ.act x : T[τ]

theorem TypingSubst.lift {σ τ Δ Δ' Γ Γ' A}
  (m : TypingSubst σ τ Δ Δ' Γ Γ') (wf : ListWf Δ A)
  : TypingSubst (σ.lift [Ty] A.length) τ Δ Δ' (A ++ Γ) (A ++ Γ')
:= ⟨m.ty, λ {x T} j =>
  match x.decLt A.length with
  | isTrue h =>
    have lem1 := List.getElem?_append_left h ▸ j
    have lem2 : x < A[τ].length := by simp [h]
    have j' : Δ'&(A[τ] ++ Γ'[τ]) ⊢ .var x : T[τ] := .var
      (by simp [List.getElem?_append_left lem2]; norm_subst [lem1])
      (.subst m.ty $ wf.get lem1)
    simp% [-Subst.lift, Subst.lift_act_lt h] j'
  | isFalse h =>
    have h : x ≥ A.length := by lia
    have lem1 := List.getElem?_append_right h ▸ j
    have lem2 := (m.act lem1).rename (.id Δ') (.add Γ'[τ] A[τ])
    simp% [-Subst.lift, Subst.lift_act_ge h] lem2⟩

theorem TypingSubst.lift_ty {σ τ Δ Δ' Γ Γ'} (m : TypingSubst σ τ Δ Δ' Γ Γ')
  : TypingSubst (σ >> RenVec.add [Term, Ty] [0, 1]) (τ.lift)
    (() :: Δ) (() :: Δ')
    Γ⟨.add Ty 1⟩ Γ'⟨.add Ty 1⟩
:= ⟨.lift m.ty, λ {x T} j =>
  have ⟨_, h⟩ := List.getElem?_eq_some_iff.1 j
  have lem1 := congrArg (λ x => x⟨.sub Ty 1⟩) j
  have lem2 := @m.act x T⟨.sub Ty 1⟩ $ simp% lem1
  simp% [<-h] lem2.rename (.succ Δ') (.id Γ'[τ])⟩

theorem Typing.kinded {Δ Γ t A} : Δ&Γ ⊢ t : A -> Δ ⊢ A type
| var j1 j2 => j2
| app j1 j2 =>
  match j1.kinded with
  | .arrow j1' j3 => j3
| lam j1 j2 => Kinding.arrow j1 j2.kinded
| tapp j1 j2 e =>
  match j1.kinded with
  | .all j1' => Kinding.beta j2 j1' |> cast (by simp [e])
| tlam j => Kinding.all j.kinded
| zero => Kinding.nat
| succ j => j.kinded
| nrec j1 j2 j3 => j1.kinded

theorem Typing.subst {Δ Δ' Γ Γ' A t} {σ : Subst Term} {τ : Subst Ty}
  (mσ : TypingSubst σ τ Δ Δ' Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'[τ] ⊢ t[σ, τ] : A[τ]
| var (x := x) j1 j2 => mσ.act j1
| app j1 j2 => app (j1.subst mσ) (j2.subst mσ)
| lam (A := A) j1 j2 => lam (j1.subst mσ.ty) (simp% j2.subst $ mσ.lift (.cons j1 .nil))
| tapp j1 j2 e => tapp (j1.subst mσ) (j2.subst mσ.ty) (by simp [e])
| tlam j => tlam (simp% j.subst $ mσ.lift_ty)
| zero => zero
| succ j => succ (j.subst mσ)
| nrec j1 j2 j3 =>
  have wf := ListWf.cons j1.kinded $ .cons j3.kinded .nil
  nrec (j1.subst mσ) (simp% j2.subst $ mσ.lift wf) (j3.subst mσ)

end SystemFWithNat
