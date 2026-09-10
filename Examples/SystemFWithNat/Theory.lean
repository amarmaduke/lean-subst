
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
  P' = P[su A::𝐬0] ->
  Typing Δ Γ (.tapp f A) P'
| tlam {Δ Γ P t} :
  Typing (.unit::Δ) Γ⟨𝐫1(Ty)⟩ t P ->
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

theorem KindingRen.succ {A X} : KindingRen (.succ Ty) X (A::X) := ⟨λ h => h⟩

theorem KindingRen.lift {Δ Δ' : List Unit} (r : Ren Ty) (h : KindingRen r Δ Δ')
  : KindingRen r.lift (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => j
    | _ + 1 => h.act j⟩

theorem Kinding.rename {Δ Δ' A} {r : Ren Ty} (m : KindingRen r Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A⟨r⟩ type
| var j => var (m.act j)
| nat => nat
| arrow j1 j2 => arrow (j1.rename m) (j2.rename m)
| all j => all (j.rename $ m.lift)

structure KindingSubst (σ : Subst Ty) (Δ Δ' : List Unit) where
  act : ∀ {x : Nat} {T}, Δ[x]? = some T -> Δ' ⊢ σ.act x type

theorem KindingSubst.lift {Δ Δ' : List Unit} {σ : Subst Ty} (m : KindingSubst σ Δ Δ')
  : KindingSubst σ.lift (.unit::Δ) (.unit::Δ')
:= ⟨λ {x} _ j =>
    match x with
    | 0 => .var j
    | _ + 1 =>
      have lem := (m.act j).rename (Δ' := .unit::Δ') KindingRen.succ
      by simp at lem; exact lem⟩

theorem Kinding.subst {Δ Δ' A} {σ : Subst Ty} (m : KindingSubst σ Δ Δ') : Δ ⊢ A type -> Δ' ⊢ A[σ] type
| var j => m.act j
| nat => nat
| arrow j1 j2 => arrow (j1.subst m) (j2.subst m)
| all j => all (j.subst $ m.lift)

structure TypingRen (r : RenVec [Term, Ty]) (Δ Δ' : List Unit) (Γ Γ' : List Ty) where
  act : (∀ {x T}, Δ[x]? = some T -> Δ'[r.2.1.act x]? = some T)
    ∧ (∀ {x T} (ξ : Ren Ty), Γ⟨ξ⟩[x]? = some T -> Γ'⟨ξ⟩[r.1.act x]? = some T)

theorem TypingRen.lift {Δ Δ' Γ Γ'} {r : RenVec [Term, Ty]} :
  ∀ (_ : TypingRen r Δ Δ' Γ Γ') (U : List Unit) (T : List Ty),
  TypingRen (r.lift [T.length, U.length])
    (U ++ Δ) (U ++ Δ')
    (T ++ Γ⟨Ren.add Ty U.length⟩) (T ++ Γ'⟨Ren.add Ty U.length⟩)
| ⟨⟨act1, act2⟩⟩, U, T =>
  ⟨⟨λ {x T'} j =>
    match Nat.decLt x (U.length) with
    | .isFalse h => by simp; grind
    | .isTrue h => by simp; grind,
    λ {x T'} (ξ : Ren Ty) j =>
    match Nat.decLt x ((T⟨ξ⟩ : List Ty).length) with
    | .isFalse h =>
      have lem0 : T.length = (T⟨ξ⟩ : List Ty).length := by rw [List.rmap_length]
      have lem1 : Γ'⟨Ren.add Ty U.length >> ξ⟩[r.1.act (x - T.length)]? = some T' := by
        simp at j; rw [List.getElem?_append_right] at j; rw [<-lem0] at j
        apply act2 (Ren.add Ty U.length >> ξ) j; grind
      by {
        simp; rw [lem0]; rw [Ren.lift_action_ge]
        rw [List.getElem?_append_right]; simp
        rw [<-lem0]; exact lem1
        grind; grind
      }
    | .isTrue h => by {
      have lem0 : T.length = (T⟨ξ⟩ : List Ty).length := by rw [List.rmap_length]
      have lem1 : x < T.length := by grind
      simp_all; grind
    }⟩⟩

theorem TypingRen.kind {Δ Δ' Γ Γ'} {r : RenVec [Term, Ty]}
  : TypingRen r Δ Δ' Γ Γ' -> KindingRen r.2.1 Δ Δ'
| ⟨act⟩ => ⟨act.1⟩

theorem Typing.rename {Δ Δ' Γ Γ' A t} {r : RenVec [Term, Ty]} (m : TypingRen r Δ Δ' Γ Γ')
  : Δ&Γ ⊢ t : A -> Δ'&Γ'⟨r.2.1⟩ ⊢ t⟨r,⟩ : A⟨r.2.1⟩
| var (x := x) j1 j2 =>
  have e := congr (f₁ := λ t => t⟨r.2.1⟩) rfl $ @m.act.2 x A 𝐫0 (j1 |> cast (by simp))
  var (e |> cast (by simp)) (j2.rename m.kind)
| app j1 j2 => app (j1.rename m) (j2.rename m)
| lam (A := A) j1 j2 =>
  have m' : TypingRen (r.lift [1, 0]) Δ Δ' (A::Γ) (A::Γ') := m.lift [] [A] |> cast (by simp)
  lam (j1.rename m.kind) (j2.rename m')
| tapp j1 j2 e => tapp (j1.rename m) (j2.rename m.kind) (by simp [e])
| tlam j =>
  have m' : TypingRen (r.lift [0, 1]) (()::Δ) (()::Δ') Γ⟨𝐫1(Ty)⟩ Γ'⟨𝐫1(Ty)⟩ := m.lift [.unit] []
  tlam (j.rename m' |> cast (by simp; grind))
| zero => zero
| succ j => succ (j.rename m)
| nrec j1 j2 j3 =>
  have m' : TypingRen (r.lift [2, 0]) Δ Δ' (A::.nat::Γ) (A::.nat::Γ') := m.lift [] [A, .nat] |> cast (by simp)
  nrec (j1.rename m) (j2.rename m') (j3.rename m)

end SystemFWithNat
