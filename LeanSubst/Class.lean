import LeanSubst.Basic
import LeanSubst.Ops

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

class RenMapId (S : Type u1) (T : Type u2) [RenMap S T] where
  apply_id {s : S} : s⟨.id T⟩ = s

class RenMapCompose (S : Type u1) (T : Type u2) [RenMap S T] where
  apply_compose {s : S} {r1 r2 : Ren T} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

@[simp]
theorem Ren.apply_id [RenMap S T] [RenMapId S T] {s : S} : s⟨id T⟩ = s := RenMapId.apply_id

@[simp, grind =]
theorem Ren.apply_compose [RenMap S T] [RenMapCompose S T] {s : S} {r1 r2 : Ren T}
  : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩
:= RenMapCompose.apply_compose

instance (priority := high) [RenMap T T] [RenMapId T T] : RenMapId (Action T) T where
  apply_id := by intro s; cases s <;> simp

instance [RenMap S T] [RenMapId S T] : RenMapId (Action S) T where
  apply_id := by intro s; cases s <;> simp

instance (priority := high) [RenMap T T] [RenMapCompose T T] : RenMapCompose (Action T) T where
  apply_compose := by intro s; cases s <;> simp

instance [RenMap S T] [RenMapCompose S T] : RenMapCompose (Action S) T where
  apply_compose := by intro s; cases s <;> simp

class SubstMapId (S : Type u1) (T : Type u2) [SubstMap S T] where
  apply_id {s : S} : s[.id T] = s

class SubstMapStable (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S T] where
  apply_stable (r : Ren T) (σ : Subst T) : r.to = σ -> rmap (S := S) r = smap σ

class SubstMapRenComposeLeft (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S T] where
  apply_ren_compose_left {s : S} {r : Ren T} {τ : Subst T} : s⟨r⟩[τ] = s[r ∘ τ]

class SubstMapRenComposeRight (T : Type u2) [RenMap T T] [SubstMap T T] where
  apply_ren_compose_right {t : T} {r : Ren T} {σ : Subst T} : t[σ]⟨r⟩ = t[σ ∘ r]

class SubstMapCompose (S : Type u1) (T : Type u2) [SubstMap S T] [SubstMap T T] where
  apply_compose {s : S} {σ τ : Subst T} : s[σ][τ] = s[σ ∘ τ]

class SubstMapRenCommute (S : Type u1) (T : Type u2) [RenMap S S] [SubstMap S T] where
  apply_ren_commute {s : S} (r : Ren S) (τ : Subst T) : s⟨r⟩[τ] = s[τ]⟨r⟩

class SubstMapHetCompose (S : Type u1) (T : Type u2) [SubstMap S S] [SubstMap S T] where
  apply_hcompose {s : S} {σ : Subst S} {τ : Subst T} : s[σ][τ] = s[τ][σ ◾ τ]

namespace Subst
  export SubstMapStable (apply_stable)
  export SubstMapRenComposeLeft (apply_ren_compose_left)
  export SubstMapRenComposeRight (apply_ren_compose_right)
  export SubstMapRenCommute (apply_ren_commute)
end Subst

@[simp, grind =]
theorem Subst.apply_id [SubstMap S T] [SubstMapId S T] {s : S} : s[.id T] = s := SubstMapId.apply_id

@[simp, grind =]
theorem Subst.apply_compose [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]
  {s : S} {σ τ : Subst T}
  : s[σ][τ] = s[σ ∘ τ]
:= SubstMapCompose.apply_compose

end LeanSubst
