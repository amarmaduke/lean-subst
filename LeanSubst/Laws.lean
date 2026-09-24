
import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class
import LeanSubst.Types.Nat
import LeanSubst.Types.List

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

-- @[grind <-]
-- theorem Ren.lift_eq_from_eq [RenMap T (T::V)] {r : Ren T} {σ : Subst T}
--   : r.to = σ -> r.to.lift = σ.lift
-- := by intro h; rw [<-h]

namespace Subst

  section

    open SubstMap

    @[simp, grind =]
    theorem I_lift [RenMap T (T::V)] {k} : 𝐬0.lift V k = id T := by
      funext; case _ x =>
      cases x; all_goals (simp [lift, id, act, SubstAction.act])
      sorry


    -- @[simp]
    -- theorem rewrite3_append [SubstMap T [T]] {σ τ : Subst T} {ℓ : List (Action T)}
    --   : (ℓ ++ σ) >> τ = ℓ[τ] ++ (σ >> τ)
    -- := by
    --   induction ℓ generalizing σ τ <;> simp
    --   case _ hd tl ih =>
    --   cases hd <;> simp [*]

    -- @[simp]
    -- theorem rewrite3_append_act [SubstMap T [T]] {σ τ : Subst T} {ℓ : List Nat}
    --   : (ℓ ++ σ) >> τ = τ.act ℓ ++ (σ >> τ)
    -- := by induction ℓ generalizing σ τ <;> simp [*]

    -- @[simp]
    -- theorem rewrite3_append_ren [RenMap T [T]] [SubstMap T [T]] {σ : Subst T} {r : Ren T} {ℓ : List Nat}
    --   : (ℓ ++ σ) >> r = ℓ⟨r⟩ ++ (σ >> r)
    -- := by
    --   induction ℓ generalizing σ r <;> simp
    --   case _ hd tl ih =>
    --   cases hd <;> simp [*]

    -- @[simp]
    -- theorem rewrite4_cons [SubstMap T (T::V)] {s} {σ : Subst T} : 𝐬1 >> (s .: σ) = σ := by
    --   simp [Subst.cons]
    --   funext; case _ x =>
    --   cases x; all_goals (simp [HAndThen.hAndThen, AndThen.andThen, compose, succ, act, SubstAction.act])

    -- @[simp]
    -- theorem rewrite4_cons_ren [SubstMap T [T]]  {s} {σ : Subst T} : Ren.succ T >> (s :: σ) = σ := by
    --   simp [Subst.cons]
    --   funext; case _ x =>
    --   cases x; all_goals (simp [HAndThen.hAndThen, compose_ren_left, act, SubstAction.act])

    -- @[simp, grind =]
    -- theorem rewrite5 [SubstMap T [T]] {σ : Subst T} : σ.act 0 :: (𝐬1 >> σ) = σ := by
    --   simp [cons, HAndThen.hAndThen, AndThen.andThen, compose]; congr
    --   funext; case _ x =>
    --   cases x <;> simp [act, SubstAction.act]

    -- @[simp]
    -- theorem rewrite5_ren [SubstMap T [T]] {σ : Subst T} : σ.act 0 :: (Ren.succ T >> σ) = σ := by
    --   simp [Subst.cons]; congr
    --   funext; case _ x =>
    --   cases x <;> simp [act, SubstAction.act]
  end

  @[grind =]
  theorem rewrite_lift [RenMap T (T::V)] {σ : Subst T}
    : σ.lift V = re 0 .: (σ >> (𝐫1(T) .: RenVec.id V))
  := by
    simp [AltCons.altCons, cons, lift]
    funext; case _ x =>
    cases x <;> simp [RenVec.cons]

  @[simp, grind =]
  theorem rewrite_lift_zero [RenMap T (T::V)] [RenMapId T (T::V)] {σ : Subst T}
    : σ.lift V 0 = σ
  := by
    simp [lift, act, SubstAction.act]
    simp [RenMap.rmap]
    sorry

  @[grind =]
  theorem rewrite_lift_succ
    [RenMap T (T::V)] [RenMapId T (T::V)] [RenMapCompose T (T::V)]
    {k} {σ : Subst T}
    : σ.lift V (k + 1) = (σ.lift V k).lift V
  := by
    sorry

  @[simp]
  theorem rewrite4_append_direct [SubstMapAll [T]] [SubstMapCompose T [T]] [SubstMapEmpty T]
    {ℓ : List $ Action T} {σ : Subst T}
    : (add T ℓ.length) >> (ℓ ++ σ) = σ
  := by
    induction ℓ generalizing σ <;> simp
    case _ hd tl ih =>
    rw [compose_add_succ_right]
    simp [*]

  @[simp]
  theorem rewrite4_append_indirect [SubstMapAll [T]] [SubstMapCompose T [T]] [SubstMapEmpty T]
    {k} {ℓ : List $ Action T} {σ : Subst T} (h : k = ℓ.length)
    : (add T k) >> (ℓ ++ σ) = σ
  := by subst h; simp

  @[grind =]
  theorem subst_append_assoc {xs ys : List $ Action T} {σ : Subst T}
    : xs ++ ys ++ σ = xs ++ (ys ++ σ)
  := by
    induction xs generalizing ys σ <;> simp [*]

  @[grind =]
  theorem subst_append_assoc_nat {xs ys : List Nat} {σ : Subst T}
    : xs ++ ys ++ σ = xs ++ (ys ++ σ)
  := by
    induction xs generalizing ys σ <;> simp [*]

  @[simp]
  theorem range_act_succ {s e} {σ : Subst T} : act (succ T) (s..e) ++ σ = s.succ..e.succ ++ σ := by
    induction e generalizing s σ <;> simp
    case _ e ih =>
    simp [Ren.range]
    cases Nat.decLe s e
    case _ h2 => simp [ite]
    case _ h2 =>
      simp [ite]
      cases Nat.decLe (s + 1) e
      case _ h3 =>
        have lem : s = e := by omega
        subst lem; simp
      case _ h3 =>
        simp [*]
        rw [subst_append_assoc, ih]; simp
        rw [subst_append_assoc_nat]; simp [Ren.range]
        split
        case _ h4 => rw [subst_append_assoc_nat]; simp
        case _ h4 => omega

  @[simp]
  theorem range_act_succ_ren {s e : Nat} {σ : Subst T}
    : (s..e)⟨Ren.succ T⟩ ++ σ = s.succ..e.succ ++ σ
  := by
    sorry


  -- @[grind =]
  -- theorem rewrite_lift_k
  --   [RenMap T (T::V)] [RenMapId T (T::V)] [RenMapCompose T (T::V)]
  --   [SubstMapAll (T::V)] [SubstMapId T (T::V)] [SubstMapCompose T (T::V)]
  --   {k} {σ : Subst T}
  --   : σ.lift V k = 0..k ++ (σ >> RenVec.add V k)
  -- := by
  --   induction k generalizing σ <;> simp
  --   case _ k ih =>
  --     rw [rewrite_lift_succ, ih]
  --     simp [rewrite_lift]
  --     congr 2

end Subst

-- @[grind =]
-- theorem Subst.compose_commute_succ [RenMap T [T]] {τ : Subst T}
--   : τ >> Ren.succ T = Ren.succ T >> τ.lift
-- := by
--   simp [HAndThen.hAndThen, compose_ren_right, compose_ren_left]

-- @[grind =]
-- theorem Ren.compose_commute_succ {r : Ren T} : r >> succ T = succ T >> r.lift := by
--   simp [HAndThen.hAndThen, AndThen.andThen, compose]

-- theorem Subst.rewrite_lift_compose_ren_left_k1 [RenMap T [T]] {r : Ren T} {τ : Subst T}
--   : (r >> τ).lift = r.lift >> τ.lift
-- := by
--   simp [HAndThen.hAndThen, compose_ren_left, lift, Ren.lift, act, SubstAction.act]
--   funext; case _ x =>
--   cases x <;> simp

-- @[simp]
-- theorem Subst.rewrite_lift_compose_ren_left
--   [RenMap T [T]] [RenMapId T [T]] [RenMapCompose T [T]]
--   {k} {r : Ren T} {τ : Subst T}
--   : (r >> τ).lift k = r.lift k >> τ.lift k
-- := by
--   induction k generalizing r τ; congr
--   case _ k ih =>
--     rw [rewrite_lift_succ, ih]
--     rw [rewrite_lift_compose_ren_left_k1]
--     rw [<-rewrite_lift_succ]
--     rw [<-Ren.lift_of_succ]

-- theorem Subst.rewrite_lift_compose_ren_left_vec :
--   ∀ {V : List (Type u2)} [RenMapLaws V]
--   {k : List Nat} {r : RenVec V} {τ : SubstVec V},
--   (r >> τ).lift k = r.lift k >> τ.lift k
-- | [], _, k, r, τ => by simp
-- | .cons _ _, _, [], (r, rs), (τ, τs) => by simp
-- | .cons _ _, @RenMapLaws.cons _ _ _ _ _ _ _ _ _, .cons k ks, (r, rs), (τ, τs) => by
--   have ih := rewrite_lift_compose_ren_left_vec (k := ks) (r := rs) (τ := τs)
--   simp [ih]

-- theorem Subst.lift_compose_ren_right_k1
--   [RenMap T [T]] [RenMapId T [T]] [RenMapCompose T [T]]
--   {σ : Subst T} {r : Ren T}
--   : (σ >> r).lift = σ.lift >> r.lift
-- := by
--   simp [lift, act, SubstAction.act]; congr; funext; case _ x =>
--   cases x <;> simp [act, SubstAction.act]; case _ x =>
--   simp [HAndThen.hAndThen, AndThen.andThen, compose_ren_right, RenVec.compose, act, SubstAction.act]
--   congr 1

-- @[simp]
-- theorem Subst.lift_compose_ren_right
--   [RenMap T [T]] [SubstMap T [T]] [RenMapId T [T]] [RenMapCompose T [T]]
--   {k} {σ : Subst T} {r : Ren T}
--   : (σ >> r).lift k = σ.lift k >> r.lift k
-- := by
--   induction k generalizing σ r; simp
--   case _ k ih =>
--     rw [rewrite_lift_succ, ih]
--     rw [lift_compose_ren_right_k1]
--     rw [<-rewrite_lift_succ]
--     rw [<-Ren.lift_of_succ]

-- theorem Subst.lift_compose_ren_right_vec :
--   ∀ {V : List (Type u2)} [SubstMapAll V] [RenMapAll V]
--   {k} {σ : SubstVec V} {r : RenVec V},
--   (σ >> r).lift k = σ.lift k >> r.lift k
-- := sorry

-- theorem Subst.rewrite_lift_compose_k1
--   [RenMapAll [T]] [SubstMap T [T]] [RenMapEmpty T]
--   [SubstMapRenComposeLeft T [T]] [SubstMapRenComposeRight T [T]]
--   {σ τ : Subst T}
--   : (σ >> τ).lift = σ.lift >> τ.lift
-- := by
--   simp [HAndThen.hAndThen, AndThen.andThen, compose, lift, act, SubstAction.act]
--   funext; case _ x =>
--   cases x <;> simp [act, SubstAction.act]
--   case _ x =>
--   cases σ.inner x
--   case re i =>
--     simp [HAndThen.hAndThen, compose_ren_left]
--     cases τ; case _ f =>
--     simp [Subst.act, SubstAction.act]
--     simp [RenMap.rmap, rmap0]
--   case su t =>
--     simp [HAndThen.hAndThen, SubstVec.compose_ren_right, compose_ren_right]
--     simp [compose_ren_left]
--     congr

@[simp]
theorem Subst.lift_zero [RenMap T (T::V)] [RenMapId T (T::V)] {σ : Subst T} : σ.lift V 0 = σ := by
  cases σ; case _ f =>
  simp [lift]; funext; case _ i =>
  cases (f i) <;> simp [RenVec.cons]
  case _ t =>
  have lem := RenMapId.apply_id (V := T::V) (s := t)
  simp [RenVec.id] at lem; exact lem

theorem Subst.lift_succ [RenMap T (T::V)] {σ : Subst T} {k}
  : σ.lift V (k + 1) = (σ.lift V k).lift V
:= by
  simp [lift]; funext; case _ i =>
  cases i <;> simp; case _ i =>
  cases Nat.decLt i k
  case _ h =>
    simp [ite, act, SubstAction.act]
    simp [RenMap.rmap, rmap0]
    cases (σ.act (i - k)) <;> simp
    case re x =>
      sorry
    case su t =>
      sorry
  case _ h => simp [ite, RenVec.cons]

@[simp]
theorem SubstVec.lift_empty [RenMapAll V] {σ : SubstVec V} : σ.lift [] = σ := sorry

@[simp]
theorem SubstVec.lift_singleton_zero [RenMapAll V] {σ : SubstVec V} : σ.lift [0] = σ := sorry

theorem SubstVec.lift_singleton_succ [RenMapAll V] {σ : SubstVec V} (k) : σ.lift [k + 1] = (σ.lift [k]).lift [1] := sorry

theorem SubstVec.succ_lift_commute [RenMapAll (T::V)] {τ : Subst T} {τs : SubstVec V}
  : (τ .: τs) >> 𝐫1(T) .: RenVec.id V = 𝐫1(T) .: RenVec.id V >> (τ.lift V .: τs)
:= by
  simp [SubstVec.cons, RenVec.cons, HAndThen.hAndThen, compose_ren_left, compose_ren_right]
  sorry

theorem Subst.lift1_compose
  [inst : RenMapAll (T::V)] [SubstMap T (T::V)]
  [SubstMapRenComposeLeft T (T::V)] [SubstMapRenComposeRight T (T::V)]
  {σ : Subst T} {τ : SubstVec $ T::V}
  : (σ >> τ).lift V = σ.lift V >> τ.lift [1]
:= by
  rcases τ with ⟨τ, τs⟩
  simp [HAndThen.hAndThen, compose, act, SubstAction.act]
  conv => lhs; simp [lift, SubstMap.smap]
  simp; funext; case _ i =>
  cases i; simp [SubstMap.smap, lift]
  case _ i =>
    simp [SubstMap.smap]
    generalize zdef : (lift V σ).inner (i + 1) = z
    simp [lift, RenMap.rmap, act, SubstAction.act] at zdef
    cases inst; case _ inst _ _ _ =>
    simp at zdef
    generalize wdef : σ.inner i = w at *
    cases w <;> simp at *
    case re x =>
      subst zdef; simp [act, SubstAction.act]
      simp [lift, RenVec.cons, act, SubstAction.act]
      simp [RenMap.rmap, rmap0, act, SubstAction.act]
    case su t =>
      subst zdef; simp
      rw [SubstMapRenComposeLeft.apply_ren_compose_left]
      rw [@SubstMapRenComposeRight.apply_ren_compose_right _ _ _ (.cons inst)]
      sorry
      -- have lem := @SubstVec.succ_lift_commute T V inst.cons τ τs
      -- simp [SubstVec.cons] at *
      -- rw [lem]

@[simp]
theorem Subst.lift_compose
  [RenMapAll (T::V)] [SubstMap T (T::V)] [RenMapId T (T::V)]
  [SubstMapRenComposeLeft T (T::V)] [SubstMapRenComposeRight T (T::V)]
  {k} {σ : Subst T} {τ : SubstVec $ T::V}
  : (σ >> τ).lift V k = σ.lift V k >> τ.lift [k]
:= by
  induction k generalizing σ τ
  rcases τ with ⟨τ, τs⟩; simp [SubstVec.lift]
  case _ k ih =>
  rw [lift_succ, ih, lift1_compose, <-lift_succ]
  rw [<-SubstVec.lift_singleton_succ]

@[simp]
theorem SubstVec.lift_singleton_compose
  [RenMapAll V] [SubstMapAll V]
  {k} {σ τ : SubstVec V}
  : (σ >> τ).lift [k] = σ.lift [k] >> τ.lift [k]
:= by
  sorry

end LeanSubst
