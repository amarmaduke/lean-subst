
import LeanSubst.Class

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

def List.rmap [RenMap S V] (r : RenVec V) : List S -> List S
| [] => []
| .cons x xs => x⟨r,⟩ :: rmap r xs

instance [RenMap S V] : RenMap (List S) V where
  rmap := List.rmap

@[simp, grind =]
theorem List.rmap_nil [RenMap S V] {r : RenVec V} : (@List.nil S)⟨r,⟩ = [] := by
  simp [RenMap.rmap, List.rmap]

@[simp, grind =]
theorem List.rmap_cons [RenMap S V] {x} {xs : List S} {r : RenVec V} : (x::xs)⟨r,⟩ = x⟨r,⟩::xs⟨r,⟩ := by
  simp [RenMap.rmap, List.rmap]

instance [RenMap S V] [RenMapId S V] : RenMapId (List S) V where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S V] [RenMapCompose S V] : RenMapCompose (List S) V where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

@[simp]
theorem List.rmap_append [RenMap S V] {xs ys : List S} {r : RenVec V}
  : (xs ++ ys)⟨r,⟩ = xs⟨r,⟩ ++ ys⟨r,⟩
:= by induction xs generalizing ys <;> simp [*]

def List.smap [SubstMap S V] (σ : SubstVec V) : List S -> List S
| [] => []
| .cons x xs => x[σ,] :: smap σ xs

instance [SubstMap S V] : SubstMap (List S) V where
  smap := List.smap

@[simp, grind =]
theorem List.smap_none [SubstMap S V] {σ : SubstVec V} : (@List.nil S)[σ,] = [] := by
  simp [SubstMap.smap, List.smap]

@[simp, grind =]
theorem List.smap_some [SubstMap S V] {x} {xs : List S} {σ : SubstVec V} : (x::xs)[σ,] = x[σ,]::xs[σ,]
:= by simp [SubstMap.smap, List.smap]

instance [RenMap S V] [SubstMap S V] [SubstMapId S V] : SubstMapId (List S) V where
  apply_id := by intro t; induction t <;> simp [*]

instance [SubstMap S V] [SubstMapAll V] [SubstMapCompose S V] : SubstMapCompose (List S) V where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

end LeanSubst
