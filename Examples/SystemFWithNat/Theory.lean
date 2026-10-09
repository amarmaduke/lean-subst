
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

theorem TypingRen.lift {Γ Γ' r} (m : TypingRen r Γ Γ') (A : List Ty)
  : TypingRen (r.lift A.length) (A ++ Γ) (A ++ Γ')
:= sorry

theorem TypingRen.shift {Γ Γ' r} k : TypingRen r Γ Γ' -> TypingRen r Γ⟨.add Ty k⟩ Γ'⟨.add Ty k⟩
| ⟨act⟩ => ⟨λ {x T} h =>
  have lem : Γ⟨.add Ty k⟩[x]?⟨.sub Ty k⟩ = some T⟨.sub Ty k⟩ := sorry
  by simp at lem; sorry⟩

theorem Typing.rename {Δ Δ' Γ Γ' A t} {r1 : Ren Ty} {r2 : Ren Term}
  (m1 : KindingRen r1 Δ Δ') (m2 : TypingRen r2 Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'⟨r1⟩ ⊢ t⟨r2, r1⟩ : A⟨r1⟩
| var (x := x) j1 j2 =>
  have j1 := congr (f₁ := λ t => t⟨r1⟩) rfl $ m2.act j1
  var (lsimp j1) (j2.rename m1)
| app j1 j2 => app (j1.rename m1 m2) (j2.rename m1 m2)
| lam (A := A) j1 j2 => lam (j1.rename m1) (j2.rename m1 $ m2.lift [A])
| tapp j1 j2 e => tapp (j1.rename m1 m2) (j2.rename m1) (by simp [e])
| tlam j =>
  have m1' := m1.lift
  --have j' := j.rename (m1.lift) m2
  tlam (by simp; sorry)
  -- have m' : TypingRen (r.lift [0, 1]) (()::Δ) (()::Δ') Γ⟨𝐫1(Ty)⟩ Γ'⟨𝐫1(Ty)⟩ := m.lift [.unit] []
  -- tlam (j.rename m' |> cast (by simp; grind))
| zero => zero
| succ j => succ (j.rename m1 m2)
| nrec j1 j2 j3 => nrec (j1.rename m1 m2) (j2.rename m1 $ m2.lift [A, Ty.nat]) (j3.rename m1 m2)

end SystemFWithNat
