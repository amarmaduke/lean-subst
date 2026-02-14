import LeanSubst.Basic

namespace LeanSubst

variable {S T : Type}

def Option.smap [SubstMap S T] (σ : Subst T) : Option S -> Option S
| none => none
| some t => some t[σ:_]

instance [SubstMap S T] : SubstMap (Option S) T where
  smap := Option.smap

@[simp]
theorem Option.smap_none [SubstMap S T] {σ : Subst T}
  : (@Option.none S)[σ:_] = none
:= by
  simp [SubstMap.smap, Option.smap]

@[simp]
theorem Option.smap_some [SubstMap S T] {x : S} {σ : Subst T}
  : (some x)[σ:_] = some x[σ:_]
:= by
  simp [SubstMap.smap, Option.smap]
