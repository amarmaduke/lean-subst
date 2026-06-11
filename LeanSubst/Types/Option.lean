
import LeanSubst.Laws

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

def Option.rmap [i : RenMap S T] (r : Ren T) : Option S -> Option S
| none => none
| some t => some t⟨r⟩

instance [RenMap S T] : RenMap (Option S) T where
  rmap := Option.rmap

@[simp, grind =]
theorem Option.rmap_none [RenMap S T] {r : Ren T} : (@Option.none S)⟨r⟩ = none := by
  simp [RenMap.rmap, Option.rmap]

@[simp, grind =]
theorem Option.rmap_some [RenMap S T] {x : S} {r : Ren T} : (some x)⟨r⟩ = some x⟨r⟩ := by
  simp [RenMap.rmap, Option.rmap]

instance [RenMap S T] [RenMapId S T] : RenMapId (Option S) T where
  apply_id := by intro t; cases t <;> simp

instance [RenMap S T] [RenMapCompose S T] : RenMapCompose (Option S) T where
  apply_compose := by intro s σ τ; cases s <;> simp

def Option.smap [SubstMap S T] (σ : Subst T) : Option S -> Option S
| none => none
| some t => some t[σ]

instance [SubstMap S T] : SubstMap (Option S) T where
  smap := Option.smap

@[simp, grind =]
theorem Option.smap_none [SubstMap S T] {σ : Subst T} : (@Option.none S)[σ] = none := by
  simp [SubstMap.smap, Option.smap]

@[simp, grind =]
theorem Option.smap_some [SubstMap S T] {x : S} {σ : Subst T} : (some x)[σ] = some x[σ] := by
  simp [SubstMap.smap, Option.smap]

instance [RenMap S T] [SubstMap S T] [SubstMapId S T] : SubstMapId (Option S) T where
  apply_id := by intro t; cases t <;> simp

instance [SubstMap T T] [SubstMap S T] [SubstMapCompose S T] : SubstMapCompose (Option S) T where
  apply_compose := by intro s σ τ; cases s <;> simp

end LeanSubst
