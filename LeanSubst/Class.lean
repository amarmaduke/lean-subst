import LeanSubst.Basic
import LeanSubst.Ops

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

class RenMapId (S : Type u1) (V : List (Type u2)) [RenMap S V] where
  apply_id {s : S} : s⟨.id V,⟩ = s

@[simp]
theorem Ren.apply_id [RenMap S V] [RenMapId S V] {s : S} : s⟨.id V,⟩ = s := RenMapId.apply_id

@[simp]
theorem Ren.apply_id1 [RenMap S [T]] [RenMapId S [T]] {s : S} : s⟨id T⟩ = s := RenMapId.apply_id

@[simp]
theorem Ren.apply_id2 [RenMap S [T1, T2]] [RenMapId S [T1, T2]] {s : S} : s⟨id T1, id T2⟩ = s := RenMapId.apply_id

class RenMapCompose (S : Type u1) (V : List (Type u2)) [RenMap S V] where
  apply_compose {s : S} {r1 r2 : RenVec V} : s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩

@[simp, grind =]
theorem Ren.apply_compose [RenMap S V] [RenMapCompose S V] {s : S} {r1 r2 : RenVec V}
  : s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
:= RenMapCompose.apply_compose

@[simp, grind =]
theorem Ren.apply_compose1 [RenMap S [T]] [RenMapCompose S [T]] {s : S} {r1 r2 : Ren T}
  : s⟨r1⟩⟨r2⟩ = s⟨r1 >> r2⟩
:= Ren.apply_compose

@[simp, grind =]
theorem Ren.apply_compose2 [RenMap S [T1, T2]] [RenMapCompose S [T1, T2]]
  {s : S} {r1 r2 : Ren T1} {k1 k2 : Ren T2}
  : s⟨r1, k1⟩⟨r2, k2⟩ = s⟨r1 >> r2, k1 >> k2⟩
:= Ren.apply_compose

instance (priority := high) [RenMap T [T]] [RenMapId T [T]] : RenMapId (Action T) [T] where
  apply_id := by intro s; cases s <;> simp [RenVec.id]

instance (priority := low) [RenMap S V] [RenMapId S V] : RenMapId (Action S) V where
  apply_id := by intro s; cases s <;> simp

instance (priority := high) [RenMap T [T]] [RenMapCompose T [T]] : RenMapCompose (Action T) [T] where
  apply_compose := by
    intro s r1 r2; cases s
    all_goals
      simp [RenVec] at r1 r2
      simp [rmap, HAndThen.hAndThen, AndThen.andThen, RenVec.compose, Ren.compose]

instance (priority := low) [RenMap S V] [RenMapCompose S V] : RenMapCompose (Action S) V where
  apply_compose := by intro s; cases s <;> simp

class SubstMapStable (S : Type u1) (V : List $ Type u2) [RenMap S V] [SubstMap S V] where
  apply_stable (r : RenVec V) (σ : SubstVec V) : r.to = σ -> rmap (S := S) r = smap σ

class SubstMapId (S : Type u1) (V : List $ Type u2) [SubstMap S V] where
  apply_id {s : S} : s[.id V,] = s

@[simp]
theorem Subst.apply_id [SubstMap S V] [SubstMapId S V] {s : S} : s[.id V,] = s := SubstMapId.apply_id

@[simp]
theorem Subst.apply_id1 [SubstMap S [T]] [SubstMapId S [T]] {s : S} : s[id T] = s := SubstMapId.apply_id

@[simp]
theorem Subst.apply_id2 [SubstMap S [T1, T2]] [SubstMapId S [T1, T2]] {s : S} : s[id T1, id T2] = s := SubstMapId.apply_id

class SubstMapRenComposeLeft (S : Type u1) (V : List $ Type u2) [RenMap S V] [SubstMap S V] where
  apply_ren_compose_left {s : S} {r : RenVec V} {τ : SubstVec V} : s⟨r,⟩[τ,] = s[r >> τ,]

@[simp, grind =]
theorem Subst.apply_ren_compose_left
  [RenMap S V] [SubstMap S V] [SubstMapRenComposeLeft S V]
  {s : S} {r : RenVec V} {σ : SubstVec V}
  : s⟨r,⟩[σ,] = s[r >> σ,]
:= SubstMapRenComposeLeft.apply_ren_compose_left

@[simp, grind =]
theorem Subst.apply_ren_compose_left1
  [RenMap S [T]] [SubstMap S [T]] [SubstMapRenComposeLeft S [T]]
  {s : S} {r : Ren T} {σ : Subst T}
  : s⟨r⟩[σ] = s[r >> σ]
:= Subst.apply_ren_compose_left

@[simp, grind =]
theorem Subst.apply_ren_compose_left2
  [RenMap S [T1, T2]] [SubstMap S [T1, T2]] [SubstMapRenComposeLeft S [T1, T2]]
  {s : S} {r1 : Ren T1} {r2 : Ren T2} {σ1 : Subst T1} {σ2 : Subst T2}
  : s⟨r1, r2⟩[σ1, σ2] = s[r1 >> σ1, r2 >> σ2]
:= Subst.apply_ren_compose_left

class SubstMapRenComposeRight (S : Type u1) (V : List $ Type u2) [RenMap S V] [RenMapAll V] [SubstMap S V] where
  apply_ren_compose_right {s : S} {r : RenVec V} {σ : SubstVec V} : s[σ,]⟨r,⟩ = s[σ >> r,]

@[simp, grind =]
theorem Subst.apply_ren_compose_right
  [RenMap S V] [RenMapAll V] [SubstMap S V] [SubstMapRenComposeRight S V]
  {s : S} {r : RenVec V} {σ : SubstVec V}
  : s[σ,]⟨r,⟩ = s[σ >> r,]
:= SubstMapRenComposeRight.apply_ren_compose_right

@[simp, grind =]
theorem Subst.apply_ren_compose_right1
  [RenMap S [T]] [RenMapAll [T]] [SubstMap S [T]] [SubstMapRenComposeRight S [T]]
  {s : S} {r : Ren T} {σ : Subst T}
  : s[σ]⟨r⟩ = s[σ >> r]
:= Subst.apply_ren_compose_right

@[simp, grind =]
theorem Subst.apply_ren_compose_right2
  [RenMap S [T1, T2]] [RenMapAll [T1, T2]] [SubstMap S [T1, T2]] [SubstMapRenComposeRight S [T1, T2]]
  {s : S} {r1 : Ren T1} {r2 : Ren T2} {σ1 : Subst T1} {σ2 : Subst T2}
  : s[σ1, σ2]⟨r1, r2⟩ = s[σ1 >> r1, σ2 >> r2]
:= Subst.apply_ren_compose_right

class SubstMapCompose (S : Type u1) (V : List $ Type u2) [SubstMap S V] [SubstMapAll V] where
  apply_compose {s : S} {σ τ : SubstVec V} : s[σ,][τ,] = s[σ >> τ,]

@[simp, grind =]
theorem Subst.apply_compose
  [SubstMap S V] [SubstMapAll V] [SubstMapCompose S V]
  {s : S} {σ1 σ2 : SubstVec V}
  : s[σ1,][σ2,] = s[σ1 >> σ2,]
:= SubstMapCompose.apply_compose

@[simp, grind =]
theorem Subst.apply_compose1
  [SubstMap S [T]] [SubstMap T [T]] [SubstMapCompose S [T]]
  {s : S} {σ1 σ2 : Subst T}
  : s[σ1][σ2] = s[σ1 >> σ2]
:= Subst.apply_compose

@[simp, grind =]
theorem Subst.apply_compose2
  [SubstMap S [T1, T2]] [SubstMap T1 [T1]] [SubstMap T2 [T2]] [SubstMapCompose S [T1, T2]]
  {s : S} {σ1 σ2 : Subst T1} {τ1 τ2 : Subst T2}
  : s[σ1, τ1][σ2, τ2] = s[σ1 >> σ2, τ1 >> τ2]
:= Subst.apply_compose

-- @[simp↓, grind =]
-- theorem Subst.apply_compose2 [SubstMap S [T1, T2]] [SubstMapCompose S [T1, T2]]
--   {s : S} {r1 r2 : Subst T1} {k1 k2 : Subst T2}
--   : s⟨r1, k1⟩⟨r2, k2⟩ = s⟨r1 >> r2, k1 >> k2⟩
-- := by
--   have lem := @SubstMapCompose.apply_compose S [T1, T2] _ _ s (r1, k1, .up .unit) (r2, k2, .up .unit)
--   rw [lem]; simp [Subst.compose_tuple]

-- class SubstMapRenCommute (S : Type u1) (T : Type u2) [RenMap S S] [RenMap S T] [SubstMap S T] where
--   apply_commute_ren_subst {s : S} {r : Ren S} {τ : Subst T} : s⟨r⟩[τ] = s[τ]⟨r⟩
--   apply_commute_ren_ren {s : S} {r1 : Ren S} {r2 : Ren T} : s⟨r1⟩⟨r2⟩ = s⟨r2⟩⟨r1⟩

-- class SubstMapRenHetCompose (S : Type u1) (T : Type u2) [RenMap S T] [SubstMap S S] where
--   apply_hcompose_ren {s : S} {σ : Subst S} {r : Ren T} : s[σ]⟨r⟩ = s⟨r⟩[σ ◾ r]

-- class SubstMapHetCompose (S : Type u1) (T : Type u2) [SubstMap S S] [SubstMap S T] where
--   apply_hcompose {s : S} {σ : Subst S} {τ : Subst T} : s[σ][τ] = s[τ][σ ◾ τ]

-- theorem Subst.apply_stable
--   [RenMap S T] [SubstMap S T] [SubstMapStable S T]
--   {r : Ren T} {σ : Subst T}
--   : r.to = σ -> rmap (S := S) r = smap σ
-- := SubstMapStable.apply_stable _ _

-- @[simp, grind =]
-- theorem Subst.apply_id [SubstMap S T] [SubstMapId S T] {s : S} : s[.id T] = s := SubstMapId.apply_id

-- @[simp, grind =]
-- theorem Subst.apply_ren_compose_left [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T]
--   {s : S} {r : Ren T} {τ : Subst T}
--   : s⟨r⟩[τ] = s[r >> τ]
-- := SubstMapRenComposeLeft.apply_ren_compose_left

-- @[simp, grind =]
-- theorem Subst.apply_ren_compose_right
--   [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T]
--   {s : S} {σ : Subst T} {r : Ren T}
--   : s[σ]⟨r⟩ = s[σ >> r]
-- := SubstMapRenComposeRight.apply_ren_compose_right

-- @[grind =]
-- theorem Subst.apply_commute_ren_subst
--   [RenMap S S] [RenMap S T] [SubstMap S T] [SubstMapRenCommute S T]
--   {s : S} {r : Ren S} {τ : Subst T}
--   : s⟨r⟩[τ] = s[τ]⟨r⟩
-- := SubstMapRenCommute.apply_commute_ren_subst

-- @[grind =]
-- theorem Subst.apply_commute_ren_ren
--   [RenMap S S] [RenMap S T] [SubstMap S T] [SubstMapRenCommute S T]
--   {s : S} {r1 : Ren S} {r2 : Ren T}
--   : s⟨r1⟩⟨r2⟩ = s⟨r2⟩⟨r1⟩
-- := SubstMapRenCommute.apply_commute_ren_ren

-- @[simp, grind =]
-- theorem Subst.apply_compose [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]
--   {s : S} {σ τ : Subst T}
--   : s[σ][τ] = s[σ >> τ]
-- := SubstMapCompose.apply_compose

-- @[simp, grind =]
-- theorem Subst.apply_hcompose_ren [SubstMap S S] [RenMap S T] [SubstMapRenHetCompose S T]
--   {s : S} {σ : Subst S} {r : Ren T}
--   : s[σ]⟨r⟩ = s⟨r⟩[σ ◾ r]
-- := SubstMapRenHetCompose.apply_hcompose_ren

-- @[simp, grind =]
-- theorem Subst.apply_hcompose [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
--   {s : S} {σ : Subst S} {τ : Subst T}
--   : s[σ][τ] = s[τ][σ ◾ τ]
-- := SubstMapHetCompose.apply_hcompose

end LeanSubst
