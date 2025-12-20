import LeanSubst.Basic

namespace LeanSubst

variable {T : Type} [Inhabited T] [SubstMap T]

inductive Ctx (T : Type) where
| nil : Ctx T
| cons : T -> Ctx T -> Ctx T

notation "[]" => Ctx.nil
infixr:55 "::" => Ctx.cons

@[simp]
def nth : Ctx T -> Nat -> T
| [], _ => default
| .cons h _, 0 => h
| .cons _ t, n + 1 => nth t n

@[simp]
def Ctx.dnth : Ctx T -> Nat -> T
| .nil, _ => default
| .cons h _, 0 => h[+1]
| .cons _ t, n + 1 => (dnth t n)[+1]

instance : GetElem (Ctx T) Nat T (λ _ _ => True) where
  getElem := λ Γ x _ => Ctx.dnth Γ x

@[simp]
theorem Ctx.elem_cons_zero {A : T} {Γ : Ctx T} : (A::Γ)[0] = A[+1] := by simp [getElem]

@[simp]
theorem Ctx.elem_cons_succ {A : T} {Γ : Ctx T} {x} : (A::Γ)[x + 1] = Γ[x][+1] := by simp [getElem]

end LeanSubst
