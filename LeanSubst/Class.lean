import LeanSubst.Basic
import LeanSubst.Ops

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 T3 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

class RenMapEmpty (S : Type u1) [RenMap S []] where
  apply_empty {s : S} {r : RenVec []} : rmap (V := []) r s = s

class RenMapVecDef (S : Type u1) (T : Type u2) (V : List (Type u2)) [RenMap S [T]] [RenMap S (T::V)] [RenMap S V] where
  apply_vecdef {s : S} {r : RenVec (T::V)} : s⟨r,⟩ = s⟨r.2,⟩⟨r.1⟩

@[grind =]
theorem Ren.apply_vecdef
  [RenMap S [T]] [RenMap S (T::V)] [RenMap S V] [RenMapVecDef S T V]
  {s : S} {r : RenVec (T::V)}
  : s⟨r,⟩ = s⟨r.2,⟩⟨r.1⟩
:= sorry

@[simp]
theorem Ren.apply_empty [RenMap S []] [RenMapEmpty S] {s : S} {r : RenVec []}
  : rmap (V := []) r s = s
:= RenMapEmpty.apply_empty

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

instance [RenMap S []] [RenSuffix S []] [RenMapEmpty S] : RenMapEmpty (Action S) where
  apply_empty := by intro s r; cases s <;> simp

instance [RenMap T [T]] [RenMap T (T::V)] [RenMap T V] [RenSuffix T V] [RenMapVecDef T T V] : RenMapVecDef (Action T) T V where
  apply_vecdef := sorry

instance [RenMap T [T]] [RenMap T (T::V)] [RenMap T V] [RenSuffix T V] [RenMapVecDef T T V] : RenMapVecDef (Subst T) T V where
  apply_vecdef := sorry

instance [RenMap T (T::V)] [RenMapId T (T::V)] : RenMapId (Action T) (T::V) where
  apply_id := by intro s; cases s <;> simp [RenVec.id]; sorry

instance [RenMap S V] [RenSuffix S V] [RenMapId S V] : RenMapId (Action S) V where
  apply_id := by intro s; cases s <;> simp

instance [RenMap S []] [RenSuffix S []] [RenMapEmpty S] : RenMapEmpty (Subst S) where
  apply_empty := by sorry
    -- intro s r; cases s <;> simp [RenMap.rmap, Subst.rmap]
    -- funext; case _ f i =>
    -- generalize zdef : f i = z at *
    -- cases z <;> simp

instance [RenMap T (T::V)] [RenMapId T (T::V)] : RenMapId (Subst T) (T::V) where
  apply_id := by sorry
    -- intro s; cases s
    -- simp [RenMap.rmap, Subst.rmap]; grind

instance [RenMap S V] [RenSuffix S V] [RenMapId S V] : RenMapId (Subst S) V where
  apply_id := by sorry

instance [RenMap T (T::V)] [RenMapCompose T (T::V)] : RenMapCompose (Action T) (T::V) where
  apply_compose := by
    intro s r1 r2; cases s
    all_goals
      simp [RenVec] at r1 r2
      simp [rmap, HAndThen.hAndThen, AndThen.andThen, RenVec.compose, Ren.compose]

instance [RenMap S V] [RenSuffix S V] [RenMapCompose S V] : RenMapCompose (Action S) V where
  apply_compose := by intro s; cases s <;> simp

instance [RenMap T (T::V)] [RenMapCompose T (T::V)] : RenMapCompose (Subst T) (T::V) where
  apply_compose := by sorry

instance [RenMap S V] [RenSuffix S V] [RenMapCompose S V] : RenMapCompose (Subst S) V where
  apply_compose := by sorry

class SubstMapStable (S : Type u1) (V : List $ Type u2) [RenMap S V] [SubstMap S V] where
  apply_stable (r : RenVec V) (σ : SubstVec V) : r.to = σ -> rmap (S := S) r = smap σ

@[grind <-]
theorem Subst.apply_stable
  [RenMap S V] [SubstMap S V] [SubstMapStable S V]
  {r : RenVec V} {σ : SubstVec V} (h : r.to = σ)
  : rmap (S := S) r = smap σ
:= SubstMapStable.apply_stable _ _ h

class SubstMapEmpty (S : Type u1) [SubstMap S []] where
  apply_empty {s : S} {σ : SubstVec []} : smap (V := []) σ s = s

class SubstMapVecDef (S : Type u1) (T : Type u2) (V : List (Type u2)) [SubstMap S [T]] [SubstMap S (T::V)] [SubstMap S V] where
  apply_vecdef {s : S} {σ : SubstVec (T::V)} : s[σ,] = s[σ.2,][σ.1]

@[grind =]
theorem Subst.apply_vecdef
  [SubstMap S [T]] [SubstMap S (T::V)] [SubstMap S V] [SubstMapVecDef S T V]
  {s : S} {σ : SubstVec (T::V)}
  : s[σ,] = s[σ.2,][σ.1]
:= sorry

@[simp]
theorem Subst.apply_empty [SubstMap S []] [SubstMapEmpty S] {s : S} {σ : SubstVec []}
  : SubstMap.smap (V := []) σ s = s
:= SubstMapEmpty.apply_empty

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
:= sorry

@[simp, grind =]
theorem Subst.apply_ren_compose_right2
  [RenMap S [T1, T2]] [RenMapAll [T1, T2]] [SubstMap S [T1, T2]] [SubstMapRenComposeRight S [T1, T2]]
  {s : S} {r1 : Ren T1} {r2 : Ren T2} {σ1 : Subst T1} {σ2 : Subst T2}
  : s[σ1, σ2]⟨r1, r2⟩ = s[(σ1⟨r2⟩ : Subst T1) >> r1, σ2 >> r2]
:= by
  sorry

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
  [SubstMap S [T]] [SubstMap T [T]] [SubstMapAll [T]] [SubstMapCompose S [T]]
  {s : S} {σ1 σ2 : Subst T}
  : s[σ1][σ2] = s[σ1 >> σ2]
:= by
  have lem := Subst.apply_compose (V := [T]) (s := s) (σ1 := (σ1, .nil)) (σ2 := (σ2, .nil))
  rw [lem]; simp [HAndThen.hAndThen, AndThen.andThen, SubstVec.compose]
  sorry
  --Subst.apply_compose

@[simp, grind =]
theorem Subst.apply_compose2
  [SubstMap S [T1, T2]] [SubstMapAll [T1, T2]] [SubstMapCompose S [T1, T2]]
  {s : S} {σ1 σ2 : Subst T1} {τ1 τ2 : Subst T2}
  : s[σ1, τ1][σ2, τ2] = s[σ1[τ2] >> σ2, τ1 >> τ2]
:= by
  have lem := Subst.apply_compose (V := [T1, T2]) (s := s) (σ1 := (σ1, τ1, .nil)) (σ2 := (σ2, τ2, .nil))
  rw [lem]; simp [HAndThen.hAndThen, AndThen.andThen, SubstVec.compose]
  sorry

@[simp, grind =]
theorem Subst.apply_compose3
  [SubstMap S [T1, T2, T3]] [SubstMapAll [T1, T2, T3]] [SubstMapCompose S [T1, T2, T3]]
  {s : S} {σ1 σ2 : Subst T1} {τ1 τ2 : Subst T2} {μ1 μ2 : Subst T3}
  : s[σ1, τ1, μ1][σ2, τ2, μ2] = s[σ1[τ2, μ2] >> σ2, τ1[μ2] >> τ2, μ1 >> μ2]
:= by
  have lem := Subst.apply_compose (V := [T1, T2, T3]) (s := s) (σ1 := (σ1, τ1, μ1, .nil)) (σ2 := (σ2, τ2, μ2, .nil))
  rw [lem]; simp [HAndThen.hAndThen, AndThen.andThen, SubstVec.compose]
  sorry

instance [SubstMap S []] [SubstSuffix S []] [SubstMapEmpty S] : SubstMapEmpty (Action S) where
  apply_empty := by intro s r; cases s <;> simp

instance [SubstMap T [T]] [SubstMap T (T::V)] [SubstMap T V] [SubstSuffix T V] [SubstMapVecDef T T V] : SubstMapVecDef (Action T) T V where
  apply_vecdef := sorry

instance [SubstMap T [T]] [SubstMap T (T::V)] [SubstMap T V] [SubstSuffix T V] [SubstMapVecDef T T V] : SubstMapVecDef (Subst T) T V where
  apply_vecdef := sorry

instance [SubstMap T (T::V)] [SubstMapId T (T::V)] : SubstMapId (Action T) (T::V) where
  apply_id := by intro s; cases s <;> simp [SubstVec.id]; sorry

instance [SubstMap S V] [SubstSuffix S V] [SubstMapId S V] : SubstMapId (Action S) V where
  apply_id := by intro s; cases s <;> simp

instance [SubstMap S []] [SubstSuffix S []] [SubstMapEmpty S] : SubstMapEmpty (Subst S) where
  apply_empty := by sorry
    -- intro s r; cases s <;> simp [SubstMap.rmap, Subst.rmap]
    -- funext; case _ f i =>
    -- generalize zdef : f i = z at *
    -- cases z <;> simp

instance [SubstMap T (T::V)] [SubstMapId T (T::V)] : SubstMapId (Subst T) (T::V) where
  apply_id := by sorry
    -- intro s; cases s
    -- simp [SubstMap.rmap, Subst.rmap]; grind

instance [SubstMap S V] [SubstSuffix S V] [SubstMapId S V] : SubstMapId (Subst S) V where
  apply_id := by sorry

instance [SubstMap T (T::V)] [SubstMapAll (T::V)] [SubstMapCompose T (T::V)]
  : SubstMapCompose (Action T) (T::V)
where
  apply_compose := by sorry

instance [SubstMap S V] [SubstSuffix S V] [SubstMapAll V] [SubstMapCompose S V]
  : SubstMapCompose (Action S) V
where
  apply_compose := by intro s; cases s <;> simp

instance [SubstMap T (T::V)] [SubstMapAll (T::V)] [SubstMapCompose T (T::V)]
  : SubstMapCompose (Subst T) (T::V)
where
  apply_compose := by sorry

instance [SubstMap S V] [SubstSuffix S V] [SubstMapAll V] [SubstMapCompose S V]
  : SubstMapCompose (Subst S) V
where
  apply_compose := by sorry

-- @[simp↓, grind =]
-- theorem Subst.apply_compose2 [SubstMap S [T1, T2]] [SubstMapCompose S [T1, T2]]
--   {s : S} {r1 r2 : Subst T1} {k1 k2 : Subst T2}
--   : s⟨r1, k1⟩⟨r2, k2⟩ = s⟨r1 >> r2, k1 >> k2⟩
-- := by
--   have lem := @SubstMapCompose.apply_compose S [T1, T2] _ _ s (r1, k1, .up .nil) (r2, k2, .up .nil)
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
