
import LeanSubst.Lemma

namespace LeanSubst

universe u1 u2 u3
variable {S : Sort u1}

instance : AltCons S (Nat -> S) where
  altCons s n i :=
    match i with
    | 0 => s
    | i + 1 => n i

@[simp]
theorem AltCons.seq_zero {s : S} {n : Nat -> S} : (s .: n) 0 = s := by simp [AltCons.altCons]

@[simp]
theorem AltCons.seq_succ {s : S} {n : Nat -> S} {i} : (s .: n) (i + 1) = n i := by
  simp [AltCons.altCons]

end LeanSubst
