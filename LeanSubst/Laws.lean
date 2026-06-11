
import LeanSubst.Basic
import LeanSubst.Ops
import LeanSubst.Class
import LeanSubst.Types.Nat
import LeanSubst.Types.List

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

@[grind <-]
theorem Ren.lift_eq_from_eq [RenMap T T] {r : Ren T} {σ : Subst T}
  : r.to = σ -> r.to.lift = σ.lift
:= by intro h; rw [<-h]

namespace Subst
  section
    @[simp, grind =]
    theorem rewrite1 : re 0 :: +1 = id T := by
      simp [Subst.cons, Subst.id]
      funext; case _ x =>
      cases x; all_goals simp

    open SubstMap

    @[simp, grind =]
    theorem I_lift [RenMap T T] {k} : +0.lift k = id T := by
      funext; case _ x =>
      cases x; all_goals (simp [lift, id, act])
      grind

    @[simp, grind =]
    theorem rewrite2 [SubstMap T T] {σ : Subst T} : +0 ∘ σ = σ := by
      funext; case _ x =>
      simp [compose, id, act]

    @[simp, grind =]
    theorem rewrite3_cons [SubstMap T T] {σ τ : Subst T} {a : Action T}
      : (a :: σ) ∘ τ = a[τ] :: (σ ∘ τ)
    := by
      simp [cons, compose]
      funext; case _ x =>
      cases x; all_goals simp [act]

    @[simp, grind =]
    theorem rewrite3_cons_ren [RenMap T T] [SubstMap T T] {σ : Subst T} {r : Ren T} {x : Nat}
      : (re x :: σ) ∘ r = re (r.act x) :: (σ ∘ r)
    := by
      simp [cons, compose_ren_right]
      funext; case _ x =>
      cases x; all_goals simp [act]

    @[simp, grind =]
    theorem rewrite3_append [SubstMap T T] {σ τ : Subst T} {ℓ : List (Action T)}
      : (ℓ ++ σ) ∘ τ = ℓ[τ] ++ (σ ∘ τ)
    := by
      induction ℓ generalizing σ τ <;> simp
      case _ hd tl ih =>
      cases hd <;> simp [*]

    @[simp, grind =]
    theorem rewrite3_append_act [SubstMap T T] {σ τ : Subst T} {ℓ : List Nat}
      : (ℓ ++ σ) ∘ τ = τ.act ℓ ++ (σ ∘ τ)
    := by
      sorry
      -- induction ℓ generalizing σ τ <;> simp [act]
      -- case _ hd tl ih =>
      -- cases hd <;> simp [*, act]

    @[simp, grind =]
    theorem rewrite3_append_ren [RenMap T T] [SubstMap T T] {σ : Subst T} {r : Ren T} {ℓ : List Nat}
      : (ℓ ++ σ) ∘ r = ℓ⟨r⟩ ++ (σ ∘ r)
    := by
      induction ℓ generalizing σ r <;> simp
      case _ hd tl ih =>
      cases hd <;> simp [*]

    @[simp, grind =]
    theorem rewrite4_cons [SubstMap T T]  {s} {σ : Subst T} : +1 ∘ (s :: σ) = σ := by
      simp [Subst.cons]
      funext; case _ x =>
      cases x; all_goals (simp [compose, succ, act])

    @[simp, grind =]
    theorem rewrite5 [SubstMap T T] {σ : Subst T} : σ.act 0 :: (+1 ∘ σ) = σ := by
      simp [Subst.cons, Subst.compose]; congr
      funext; case _ x =>
      cases x <;> simp [act]
  end

  @[simp, grind =]
  theorem rewrite_lift [RenMap T T] [SubstMap T T] [SubstMapStable T T] {σ : Subst T}
    : σ.lift = re 0 :: (σ ∘ +1)
  := by
    simp [Subst.cons, Subst.lift, Subst.compose]
    funext; case _ x =>
    cases x; simp
    case _ n =>
      simp [Subst.succ, act]
      generalize tdef : σ.inner n = t
      cases t <;> simp [act] at *
      case _ y =>
        rw [apply_stable (σ := +1)]
        simp [Subst.succ]
        rw [Ren.to_succ]

  @[simp, grind =]
  theorem rewrite_lift_zero [RenMap T T] [RenMapId T T] {σ : Subst T}
    : σ.lift 0 = σ
  := by simp [lift, act]

  @[grind =]
  theorem rewrite_lift_succ
    [RenMap T T] [RenMapId T T] [RenMapCompose T T]
    {k} {σ : Subst T}
    : σ.lift (k + 1) = (σ.lift k).lift
  := by
    induction k; simp
    case _ n ih =>
      replace ih (i : Nat) : (σ.lift (n + 1)).act i = ((σ.lift n).lift 1).act i := by rw [ih]
      simp [Subst.lift]
      funext; case _ i =>
      have lem := ih i
      cases i <;> simp [act]
      sorry
      -- case _ i =>
      --   simp [Subst.lift] at lem
      --   split; case _ h1 =>
      --   simp  at h1
      --   have lem2 : n ≤ i := by omega
      --   generalize zdef : σ.act (i - (n + 1)) = z
      --   cases z <;> simp; omega
      --   congr

  @[simp, grind =]
  theorem rewrite6 [RenMap T T] [SubstMap T T] [SubstMapId T T] {σ : Subst T}
    : σ ∘ +0 = σ
  := by
    sorry
    -- simp [Subst.compose, Subst.id, act]; congr
    -- funext; case _ x =>
    -- generalize zdef : σ.act x = z
    -- cases z <;> simp [act] at *; case _ s =>
    -- have lem := SubstMapId.apply_id (T := T) (s := s)
    -- simp [Subst.id] at lem; exact lem

  @[simp, grind =]
  theorem rewrite7
    [SubstMap T T] [SubstMapCompose T T]
    {σ τ μ : Subst T}
    : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ
  := by
    simp [Subst.compose, act]
    funext; case _ x =>
    cases σ.inner x <;> simp [act]
    sorry

  @[simp, grind =]
  theorem rewrite4_append_direct [SubstMap T T] [SubstMapCompose T T]
    {ℓ : List $ Action T} {σ : Subst T}
    : (add T ℓ.length) ∘ (ℓ ++ σ) = σ
  := by
    induction ℓ generalizing σ <;> simp
    case _ hd tl ih =>
    rw [compose_add_succ_right]
    simp [*]

  @[simp, grind <-]
  theorem rewrite4_append_indirect [SubstMap T T] [SubstMapCompose T T]
    {k} {ℓ : List $ Action T} {σ : Subst T} (h : k = ℓ.length)
    : (add T k) ∘ (ℓ ++ σ) = σ
  := by subst h; simp

  @[simp, grind =]
  theorem rewrite_lift_k [RenMap T T] [RenMapId T T] [RenMapCompose T T] [SubstMap T T] [SubstMapId T T] [SubstMapStable T T] {k} {σ : Subst T}
    : σ.lift k = List.range k ++ (σ ∘ add T k)
  := by
    induction k generalizing σ; simp
    case _ k ih =>
      rw [rewrite_lift_succ, ih]; simp

      sorry

  @[simp, grind =]
  theorem hrewrite1 [SubstMap S T] [SubstMapId S T] {σ : Subst S} : σ ◾ (id T) = σ := by
    simp [hcompose, act]; congr
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  -- @[simp, grind =]
  -- theorem hcomp_ren_left
  --   [RenMap S] [RenMap T] [SubstMap S T]
  --   (r : Ren) (σ : Subst T)
  --   : (@Ren.to S r) ◾ σ = r.to
  -- := by
  --   funext; case _ x =>
  --   induction x <;> simp [Subst.hcompose, Ren.to]

  @[simp, grind =]
  theorem hrewrite2 [SubstMap S T] {σ : Subst T} : (id S) ◾ σ = +0 := by simp [hcompose, id, act]

  @[simp, grind =]
  theorem hrewrite3 [SubstMap S T] {σ : Subst T} : (succ S) ◾ σ = +1 := by
    simp [hcompose, succ, act]

  @[simp, grind =]
  theorem hrewrite4
    [SubstMap S T]
    {x} {σ : Subst S} {τ : Subst T}
    : (re x :: σ) ◾ τ = re x :: (σ ◾ τ)
  := by
    simp [Subst.hcompose, act]; congr
    funext; case _ i =>
    cases i <;> simp [Subst.cons, act]

  @[grind =]
  theorem hcomp_dist_ren_left
    [SubstMap S T]
    (r : Ren S) {σ : Subst S} {τ : Subst T}
    : (r ∘ σ) ◾ τ = r ∘ σ ◾ τ
  := by
    funext; case _ x =>
    simp [hcompose, compose_ren_left, act]

  @[simp, grind =]
  theorem hrewrite5
    [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]
    {σ : Subst S} {τ μ : Subst T}
    : (σ ◾ τ) ◾ μ = σ ◾ (τ ∘ μ)
  := by
    simp [Subst.hcompose, act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  @[grind =]
  theorem hcomp_distr_ren_right
    [RenMap S S] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
    (r : Ren S) (σ : Subst S) (μ : Subst T)
    : (σ ∘ r) ◾ μ = (σ ◾ μ) ∘ r
  := by
    simp [hcompose, compose_ren_right, act]; funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp
    rw [apply_ren_commute]

  @[simp, grind =]
  theorem apply_hcompose
    [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
    {s : S} {σ : Subst S} {τ : Subst T}
    : s[σ][τ] = s[τ][σ ◾ τ]
  := by exact SubstMapHetCompose.apply_hcompose

  @[simp, grind =]
  theorem hrewrite7
    [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
    {σ τ : Subst S} (μ : Subst T)
    : (σ ∘ τ) ◾ μ = (σ ◾ μ) ∘ τ ◾ μ
  := by
    simp [Subst.hcompose, Subst.compose, act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp [Subst.hcompose, act]

  theorem hrewrite_lift1
    [RenMap S S] [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T] [SubstMapRenCommute S T]
    {σ : Subst S} {τ : Subst T}
    : (σ ◾ τ).lift = σ.lift ◾ τ
  := by
    sorry
    -- simp [Subst.lift, act]; congr; funext; case _ i =>
    -- cases i <;> simp
    -- case _ n =>
    --   generalize zdef : σ.inner n = z
    --   cases z <;> simp [act]; case _ t =>
    --   rw [SubstMapRenCommute.apply_ren_commute]

  @[simp, grind =]
  theorem hrewrite_lift
    [RenMap S S] [SubstMap S S] [SubstMap S T] [RenMapId S S] [RenMapCompose S S]
    [SubstMapHetCompose S T] [SubstMapRenCommute S T]
    {k} {σ : Subst S} {τ : Subst T}
    : (σ ◾ τ).lift k = σ.lift k ◾ τ
  := by
    induction k generalizing σ τ
    case _ => simp
    case _ i ih =>
      rw [rewrite_lift_succ]
      rw [rewrite_lift_succ]
      simp; rw [ih, hrewrite_lift1]
      grind
end Subst

@[grind =]
theorem Subst.compose_commute_succ [RenMap T T] {τ : Subst T}
  : τ ∘ Ren.succ T = Ren.succ T ∘ τ.lift
:= by congr

@[grind =]
theorem Ren.compose_commute_succ {r : Ren T} : r ∘ succ T = succ T ∘ r.lift := by simp [compose]

theorem Subst.rewrite_lift_compose_ren_left_k1 [RenMap T T] {r : Ren T} {τ : Subst T}
  : (r ∘ τ).lift = r.lift ∘ τ.lift
:= by
  simp [compose_ren_left, lift, Ren.lift, act]
  funext; case _ x =>
  cases x <;> simp

@[simp, grind =]
theorem Subst.rewrite_lift_compose_ren_left
  [RenMap T T] [RenMapId T T] [RenMapCompose T T]
  {k} {r : Ren T} {τ : Subst T}
  : (r ∘ τ).lift k = r.lift k ∘ τ.lift k
:= by
  induction k generalizing r τ; congr
  case _ k ih =>
    rw [rewrite_lift_succ, ih]
    rw [rewrite_lift_compose_ren_left_k1]
    rw [<-rewrite_lift_succ]
    rw [<-Ren.lift_of_succ]

theorem Subst.lift_compose_ren_right_k1
  [RenMap T T] [RenMapId T T] [RenMapCompose T T]
  {σ : Subst T} {r : Ren T}
  : (σ ∘ r).lift = σ.lift ∘ r.lift
:= by
  simp [lift, act]; congr; funext; case _ x =>
  cases x <;> simp [act]; case _ x =>
  simp [compose_ren_right, act]; grind

@[simp, grind =]
theorem Subst.lift_compose_ren_right
  [RenMap T T] [RenMapId T T] [RenMapCompose T T]
  {k} {σ : Subst T} {r : Ren T}
  : (σ ∘ r).lift k = σ.lift k ∘ r.lift k
:= by
  induction k generalizing σ r; simp
  case _ k ih =>
    rw [rewrite_lift_succ, ih]
    rw [lift_compose_ren_right_k1]
    rw [<-rewrite_lift_succ]
    rw [<-Ren.lift_of_succ]

theorem Subst.rewrite_lift_compose_k1
  [RenMap T T] [SubstMap T T] [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T]
  {σ τ : Subst T}
  : (σ ∘ τ).lift = σ.lift ∘ τ.lift
:= by
  simp [compose, lift, act]
  funext; case _ x =>
  cases x <;> simp [act]
  case _ x =>
  cases σ.inner x <;> simp [act]; case _ t =>
  rw [SubstMapRenComposeLeft.apply_ren_compose_left]
  rw [SubstMapRenComposeRight.apply_ren_compose_right]
  have lem := Subst.compose_commute_succ (τ := τ)
  simp [lift, act] at lem
  rw [lem]

@[simp, grind =]
theorem Subst.rewrite_lift_compose
  [RenMap T T] [RenMapId T T] [RenMapCompose T T] [SubstMap T T]
  [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T]
  {k} {σ τ : Subst T}
  : (σ ∘ τ).lift k = σ.lift k ∘ τ.lift k
:= by
  induction k generalizing σ τ; simp
  case _ k ih =>
    rw [rewrite_lift_succ, ih]
    rw [rewrite_lift_succ (σ := σ)]
    rw [rewrite_lift_succ (σ := τ)]
    rw [rewrite_lift_compose_k1]

macro "subst_solve_id" : tactic => `(tactic| {
  intro t; induction t
  any_goals solve | simp +instances [*]
  all_goals try simp at *; simp  +instances [*]; grind
})

macro "subst_solve_stable" : tactic => `(tactic| {
  intro r σ h
  funext; case _ t =>
  induction t generalizing r σ
  all_goals simp [rmap, smap, *] at *; try simp +instances [*]
  any_goals solve | (rw [<-h]; simp +instances [Ren.to])
  all_goals try repeat funext; grind
})

macro "subst_solve_compose" : tactic => `(tactic| {
  intro s σ τ
  induction s generalizing σ τ
  any_goals solve | simp +instances [*]
  try any_goals solve | (
    try simp [-Subst.rewrite_lift, *]
    try funext; case _ x =>
    try rw [<-Ren.to_lift]
    try simp [-Subst.rewrite_lift, *]
    try grind)
})

end LeanSubst
