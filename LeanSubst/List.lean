import LeanSubst.Basic

namespace LeanSubst

variable {T : Type} [Inhabited T] [RenMap T] [SubstMap T T]

@[simp]
def List.subst_get (σ : Subst T) : List T -> Nat -> T
| .nil, _ => default
| .cons h _, 0 => h[σ]
| .cons _ t, n + 1 => (subst_get σ t n)[σ]

macro:max t:term noWs "[" σ:term "|" x:term "]" : term => `(List.subst_get $σ $t $x)

@[simp]
theorem List.subst_get_zero {σ} {A : T} {Γ : List T} : (A::Γ)[σ|0] = A[σ] := by
  simp [subst_get]

@[simp]
theorem List.subst_get_succ {σ} {A : T} {Γ : List T} {x} : (A::Γ)[σ|x + 1] = Γ[σ|x][σ] := by
  simp [subst_get]

end LeanSubst
