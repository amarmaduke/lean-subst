
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

def List.rmap [RenMap S T] (r : Ren T) : List S -> List S
| [] => []
| .cons x xs => x⟨r⟩ :: rmap r xs

instance [RenMap S T] : RenMap (List S) T where
  rmap := List.rmap

@[simp, grind =]
theorem List.rmap_nil [RenMap S T] {r : Ren T} : (@List.nil S)⟨r⟩ = [] := by
  simp [RenMap.rmap, List.rmap]

@[simp, grind =]
theorem List.rmap_cons [RenMap S T] {x} {xs : List S} {r : Ren T} : (x::xs)⟨r⟩ = x⟨r⟩::xs⟨r⟩ := by
  simp [RenMap.rmap, List.rmap]

instance [RenMap S T] [RenMapId S T] : RenMapId (List S) T where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S T] [RenMapCompose S T] : RenMapCompose (List S) T where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

def List.smap [SubstMap S T] (σ : Subst T) : List S -> List S
| [] => []
| .cons x xs => x[σ] :: smap σ xs

instance [SubstMap S T] : SubstMap (List S) T where
  smap := List.smap

@[simp, grind =]
theorem List.smap_none [SubstMap S T] {σ : Subst T} : (@List.nil S)[σ] = [] := by
  simp [SubstMap.smap, List.smap]

@[simp, grind =]
theorem List.smap_some [SubstMap S T] {x} {xs : List S} {σ : Subst T} : (x::xs)[σ] = x[σ]::xs[σ]
:= by simp [SubstMap.smap, List.smap]

instance [RenMap S T] [SubstMap S T] [SubstMapId S T] : SubstMapId (List S) T where
  apply_id := by intro t; induction t <;> simp [*]

instance [SubstMap T T] [SubstMap S T] [SubstMapCompose S T] : SubstMapCompose (List S) T where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

end LeanSubst
