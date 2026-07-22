
import Lilac
open Lilac

namespace LeanSubst

universe u

def Tuple.get : ∀ {n : Nat} {α : Vec (Type u) n}, Tuple α -> (i : Fin n) -> α[i]
| 0, #(), t, i => Fin.elim0 i
| n + 1, .cons x xs, t, i =>
  match n, xs, t, i with
  | 0, #(), t, 0 => t
  | n + 1, .cons y xs, (t, ts), i => by
    cases i using Fin.cases with
    | zero => exact t
    | succ i => exact get ts i

end LeanSubst
