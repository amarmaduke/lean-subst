
import LeanSubst.Basic

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

def Option.rmap [RenMap S V] (r : RenVec V) : Option S -> Option S
| none => none
| some t => some t⟨r,⟩

instance [RenMap S V] : RenMap (Option S) V where
  rmap := Option.rmap

@[simp, grind =]
theorem Option.rmap_none [RenMap S V] {r : RenVec V} : (@Option.none S)⟨r,⟩ = none := by
  simp [RenMap.rmap, Option.rmap]

@[simp, grind =]
theorem Option.rmap_some [RenMap S V] {x : S} {r : RenVec V} : (some x)⟨r,⟩ = some x⟨r,⟩ := by
  simp [RenMap.rmap, Option.rmap]

instance [RenMap S V] [RenMapId S V] : RenMapId (Option S) V where
  id_law := by intro t; cases t <;> simp

instance [RenMap S V] [RenMapComp S V] : RenMapComp (Option S) V where
  compose_law := by intro s σ τ; cases s <;> simp

def Option.smap [SubstMap S V] (σ : SubstVec V) : Option S -> Option S
| none => none
| some t => some t[σ,]

instance [SubstMap S V] : SubstMap (Option S) V where
  smap := Option.smap

@[simp, grind =]
theorem Option.smap_none [SubstMap S V] {σ : SubstVec V} : (@Option.none S)[σ,] = none := by
  simp [SubstMap.smap, Option.smap]

@[simp, grind =]
theorem Option.smap_some [SubstMap S V] {x : S} {σ : SubstVec V} : (some x)[σ,] = some x[σ,] := by
  simp [SubstMap.smap, Option.smap]

instance [SubstMap S V] [SubstMapId S V] : SubstMapId (Option S) V where
  id_law := by intro t; cases t <;> simp

instance [SubstMapAll V] [SubstMap S V] [SubstMapComp S V] : SubstMapComp (Option S) V where
  compose_law := by intro s σ τ; cases s <;> simp

end LeanSubst
