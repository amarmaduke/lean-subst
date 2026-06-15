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

class SubstMapStable (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S T] where
  apply_stable (r : Ren T) (σ : Subst T) : r.to = σ -> rmap (S := S) r = smap σ

class SubstMapId (S : Type u1) (T : Type u2) [SubstMap S T] where
  apply_id {s : S} : s[.id T] = s

class SubstMapRenComposeLeft (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S T] where
  apply_ren_compose_left {s : S} {r : Ren T} {τ : Subst T} : s⟨r⟩[τ] = s[r ∘ τ]

class SubstMapRenComposeRight (S : Type u1) (T : Type u2) [RenMap S T] [RenMap T T] [SubstMap S T] where
  apply_ren_compose_right {s : S} {r : Ren T} {σ : Subst T} : s[σ]⟨r⟩ = s[σ ∘ r]

class SubstMapCompose (S : Type u1) (T : Type u2) [SubstMap S T] [SubstMap T T] where
  apply_compose {s : S} {σ τ : Subst T} : s[σ][τ] = s[σ ∘ τ]

class SubstMapRenCommute (S : Type u1) (T : Type u2) [RenMap S S] [RenMap S T] [SubstMap S T] where
  apply_commute_ren_subst {s : S} {r : Ren S} {τ : Subst T} : s⟨r⟩[τ] = s[τ]⟨r⟩
  apply_commute_ren_ren {s : S} {r1 : Ren S} {r2 : Ren T} : s⟨r1⟩⟨r2⟩ = s⟨r2⟩⟨r1⟩

class SubstMapRenHetCompose (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S S] where
  apply_hcompose_ren {s : S} {σ : Subst S} {r : Ren T} : s[σ]⟨r⟩ = s⟨r⟩[σ ◾ r]

class SubstMapHetCompose (S : Type u1) (T : Type u2) [SubstMap S S] [SubstMap S T] where
  apply_hcompose {s : S} {σ : Subst S} {τ : Subst T} : s[σ][τ] = s[τ][σ ◾ τ]

theorem Subst.apply_stable
  [RenMap S T] [SubstMap S T] [SubstMapStable S T]
  {r : Ren T} {σ : Subst T}
  : r.to = σ -> rmap (S := S) r = smap σ
:= SubstMapStable.apply_stable _ _

@[simp, grind =]
theorem Subst.apply_id [SubstMap S T] [SubstMapId S T] {s : S} : s[.id T] = s := SubstMapId.apply_id

@[simp, grind =]
theorem Subst.apply_ren_compose_left [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T]
  {s : S} {r : Ren T} {τ : Subst T}
  : s⟨r⟩[τ] = s[r ∘ τ]
:= SubstMapRenComposeLeft.apply_ren_compose_left

@[simp, grind =]
theorem Subst.apply_ren_compose_right
  [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T]
  {s : S} {σ : Subst T} {r : Ren T}
  : s[σ]⟨r⟩ = s[σ ∘ r]
:= SubstMapRenComposeRight.apply_ren_compose_right

@[grind =]
theorem Subst.apply_commute_ren_subst
  [RenMap S S] [RenMap S T] [SubstMap S T] [SubstMapRenCommute S T]
  {s : S} {r : Ren S} {τ : Subst T}
  : s⟨r⟩[τ] = s[τ]⟨r⟩
:= SubstMapRenCommute.apply_commute_ren_subst

@[grind =]
theorem Subst.apply_commute_ren_ren
  [RenMap S S] [RenMap S T] [SubstMap S T] [SubstMapRenCommute S T]
  {s : S} {r1 : Ren S} {r2 : Ren T}
  : s⟨r1⟩⟨r2⟩ = s⟨r2⟩⟨r1⟩
:= SubstMapRenCommute.apply_commute_ren_ren

@[simp, grind =]
theorem Subst.apply_compose [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]
  {s : S} {σ τ : Subst T}
  : s[σ][τ] = s[σ ∘ τ]
:= SubstMapCompose.apply_compose

@[simp, grind =]
theorem Subst.apply_hcompose_ren [SubstMap S S] [RenMap S T] [SubstMapRenHetCompose S T]
  {s : S} {σ : Subst S} {r : Ren T}
  : s[σ]⟨r⟩ = s⟨r⟩[σ ◾ r]
:= SubstMapRenHetCompose.apply_hcompose_ren

@[simp, grind =]
theorem Subst.apply_hcompose [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
  {s : S} {σ : Subst S} {τ : Subst T}
  : s[σ][τ] = s[τ][σ ◾ τ]
:= SubstMapHetCompose.apply_hcompose

end LeanSubst
