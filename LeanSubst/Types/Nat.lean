
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

def Nat.rmap (r : Ren T) : Nat -> Nat
| n => r.act n

instance : RenMap Nat T where
  rmap := Nat.rmap

@[simp, grind =]
theorem Nat.rmap_simp {r : Ren T} {n} : n⟨r⟩ = r.act n := by simp [RenMap.rmap, Nat.rmap]

end LeanSubst
