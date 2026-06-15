
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
    @[simp]
    theorem rewrite0 [RenMap T T] : +0σ ∘ +1r = succ T := by
      congr

    @[simp, grind =]
    theorem rewrite1 : re 0 :: +1σ = id T := by
      simp [Subst.cons, Subst.id]
      funext; case _ x =>
      cases x; all_goals simp

    @[simp, grind =]
    theorem rewrite1_ren : 0 :: +1r = Ren.id T := by
      simp [Ren.cons, Ren.id]
      funext; case _ x =>
      cases x <;> simp

    open SubstMap

    @[simp, grind =]
    theorem I_lift [RenMap T T] {k} : +0σ.lift k = id T := by
      funext; case _ x =>
      cases x; all_goals (simp [lift, id, act, SubstAction.act])
      grind

    @[simp, grind =]
    theorem rewrite2 [SubstMap T T] {σ : Subst T} : +0σ ∘ σ = σ := by
      funext; case _ x =>
      simp [compose, id, act, SubstAction.act]

    @[simp, grind =]
    theorem rewrite2_ren [SubstMap T T] {σ : Subst T} : +0r ∘ σ = σ := by
      funext; case _ x =>
      simp [compose_ren_left, act, SubstAction.act]

    @[simp, grind =]
    theorem rewrite3_cons [SubstMap T T] {σ τ : Subst T} {a : Action T}
      : (a :: σ) ∘ τ = a[τ] :: (σ ∘ τ)
    := by
      simp [cons, compose]
      funext; case _ x =>
      cases x; all_goals simp [act, SubstAction.act]

    @[simp, grind =]
    theorem rewrite3_cons_ren [RenMap T T] [SubstMap T T] {σ : Subst T} {r : Ren T} {x : Nat}
      : (re x :: σ) ∘ r = re (r.act x) :: (σ ∘ r)
    := by
      simp [cons, compose_ren_right]
      funext; case _ x =>
      cases x; all_goals simp [act, SubstAction.act]

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
    := by induction ℓ generalizing σ τ <;> simp [*]

    @[simp, grind =]
    theorem rewrite3_append_ren [RenMap T T] [SubstMap T T] {σ : Subst T} {r : Ren T} {ℓ : List Nat}
      : (ℓ ++ σ) ∘ r = ℓ⟨r⟩ ++ (σ ∘ r)
    := by
      induction ℓ generalizing σ r <;> simp
      case _ hd tl ih =>
      cases hd <;> simp [*]

    @[simp, grind =]
    theorem rewrite4_cons [SubstMap T T]  {s} {σ : Subst T} : +1σ ∘ (s :: σ) = σ := by
      simp [Subst.cons]
      funext; case _ x =>
      cases x; all_goals (simp [compose, succ, act, SubstAction.act])

    @[simp, grind =]
    theorem rewrite4_cons_ren [SubstMap T T]  {s} {σ : Subst T} : +1r ∘ (s :: σ) = σ := by
      simp [Subst.cons]
      funext; case _ x =>
      cases x; all_goals (simp [compose_ren_left, act, SubstAction.act])

    @[simp, grind =]
    theorem rewrite5 [SubstMap T T] {σ : Subst T} : σ.act 0 :: (+1σ ∘ σ) = σ := by
      simp [Subst.cons, Subst.compose]; congr
      funext; case _ x =>
      cases x <;> simp [act, SubstAction.act]

    @[simp, grind =]
    theorem rewrite5_ren [SubstMap T T] {σ : Subst T} : σ.act 0 :: (+1r ∘ σ) = σ := by
      simp [Subst.cons]; congr
      funext; case _ x =>
      cases x <;> simp [act, SubstAction.act]
  end

  @[simp, grind =]
  theorem rewrite_lift [RenMap T T] {σ : Subst T}
    : σ.lift = re 0 :: (σ ∘ +1r)
  := by
    simp [cons, lift, compose_ren_right]
    funext; case _ x =>
    cases x <;> simp

  @[simp, grind =]
  theorem rewrite_lift_zero [RenMap T T] [RenMapId T T] {σ : Subst T}
    : σ.lift 0 = σ
  := by simp [lift, act, SubstAction.act]

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
      cases i <;> simp [act, SubstAction.act]
      case _ k =>
      split <;> simp
      rw [Ren.compose_add_succ_right]

  @[simp, grind =]
  theorem rewrite6 [RenMap T T] [SubstMap T T] [SubstMapId T T] {σ : Subst T}
    : σ ∘ +0σ = σ
  := by
    simp [compose, id, act, SubstAction.act]; congr; funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp [act, SubstAction.act]
    case _ t =>
    have lem : t[id T] = t := by simp
    simp [id] at lem; exact lem

  @[simp, grind =]
  theorem rewrite6_ren [RenMap T T] [RenMapId T T] {σ : Subst T}
    : σ ∘ +0r = σ
  := by
    simp [compose_ren_right]; congr

  @[simp, grind =]
  theorem rewrite7
    [SubstMap T T] [SubstMapCompose T T]
    {σ τ μ : Subst T}
    : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ
  := by
    simp [Subst.compose, act, SubstAction.act]
    funext; case _ x =>
    cases σ.inner x <;> simp [act, SubstAction.act]
    simp [compose, act, SubstAction.act]

  @[simp, grind =]
  theorem rewrite7_ren
    [RenMap T T] [RenMapCompose T T]
    {σ : Subst T} {r1 r2 : Ren T}
    : (σ ∘ r1) ∘ r2 = σ ∘ r1 ∘ r2
  := by simp [compose_ren_right]

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
    : (s..e)⟨.succ T⟩ ++ σ = s.succ..e.succ ++ σ
  := by
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
        rw [subst_append_assoc_nat, ih]; simp
        rw [subst_append_assoc_nat]; simp [Ren.range]
        split
        case _ h4 => rw [subst_append_assoc_nat]; simp
        case _ h4 => omega

  @[simp, grind =]
  theorem rewrite_lift_k
    [RenMap T T] [RenMapId T T] [RenMapCompose T T]
    [SubstMap T T] [SubstMapId T T] [SubstMapCompose T T]
    {k} {σ : Subst T}
    : σ.lift k = 0..k ++ (σ ∘ +r k)
  := by
    induction k generalizing σ <;> simp
    case _ k ih =>
      rw [rewrite_lift_succ, ih]
      simp; congr

  @[simp, grind =]
  theorem hrewrite1 [SubstMap S T] [SubstMapId S T] {σ : Subst S} : σ ◾ (id T) = σ := by
    simp [hcompose, act, SubstAction.act]; congr
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  @[simp, grind =]
  theorem hrewrite1_ren [RenMap S T] [RenMapId S T] {σ : Subst S} : σ ◾ (.id T) = σ := by
    simp [hcompose_ren, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite2 [SubstMap S T] {σ : Subst T} : (id S) ◾ σ = +0σ := by
    simp [hcompose, id, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite2_ren [RenMap S T] {r : Ren T} : (id S) ◾ r = +0σ := by
    simp [hcompose_ren, id, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite3 [SubstMap S T] {σ : Subst T} : (succ S) ◾ σ = +1σ := by
    simp [hcompose, succ, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite3_ren [RenMap S T] {r : Ren T} : (succ S) ◾ r = +1σ := by
    simp [hcompose_ren, succ, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite4
    [SubstMap S T]
    {x} {σ : Subst S} {τ : Subst T}
    : (re x :: σ) ◾ τ = re x :: (σ ◾ τ)
  := by
    simp [Subst.hcompose, act]; congr
    funext; case _ i =>
    cases i <;> simp [Subst.cons, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite4_ren
    [RenMap S T]
    {x} {σ : Subst S} {r : Ren T}
    : (re x :: σ) ◾ r = re x :: (σ ◾ r)
  := by
    simp [hcompose_ren, act]; congr
    funext; case _ i =>
    cases i <;> simp [Subst.cons, act, SubstAction.act]

  @[grind =]
  theorem hcomp_dist_ren_left
    [SubstMap S T]
    (r : Ren S) {σ : Subst S} {τ : Subst T}
    : (r ∘ σ) ◾ τ = r ∘ σ ◾ τ
  := by
    funext; case _ x =>
    simp [hcompose, compose_ren_left, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite5_subst_subst
    [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]
    {σ : Subst S} {τ μ : Subst T}
    : (σ ◾ τ) ◾ μ = σ ◾ (τ ∘ μ)
  := by
    simp [Subst.hcompose, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  @[simp, grind =]
  theorem hrewrite5_subst_ren
    [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T]
    {σ : Subst S} {τ : Subst T} {r : Ren T}
    : (σ ◾ τ) ◾ r = σ ◾ (τ ∘ r)
  := by
    simp [hcompose_ren, hcompose, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  @[simp, grind =]
  theorem hrewrite5_ren_subst
    [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T]
    {σ : Subst S} {τ : Subst T} {r : Ren T}
    : (σ ◾ r) ◾ τ = σ ◾ (r ∘ τ)
  := by
    simp [hcompose_ren, hcompose, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp

  @[simp, grind =]
  theorem hrewrite5_ren_ren
    [RenMap S T] [SubstMap S T] [RenMapCompose S T]
    {σ : Subst S} {r1 r2 : Ren T}
    : (σ ◾ r1) ◾ r2 = σ ◾ (r1 ∘ r2)
  := by
    simp [hcompose_ren, act, SubstAction.act]

  @[grind =]
  theorem hcomp_distr_ren_right
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
    (r : Ren S) (σ : Subst S) (μ : Subst T)
    : (σ ∘ r) ◾ μ = (σ ◾ μ) ∘ r
  := by
    simp [hcompose, compose_ren_right, act, SubstAction.act]; funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp
    rw [apply_commute_ren_subst]

  @[simp, grind =]
  theorem hrewrite7
    [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
    {σ τ : Subst S} (μ : Subst T)
    : (σ ∘ τ) ◾ μ = (σ ◾ μ) ∘ τ ◾ μ
  := by
    simp [hcompose, compose, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp [hcompose, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite7_ren
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T] [SubstMapRenHetCompose S T]
    {σ τ : Subst S} {r : Ren T}
    : (σ ∘ τ) ◾ r = (σ ◾ r) ∘ τ ◾ r
  := by
    simp [hcompose_ren, compose, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp [hcompose_ren, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite8
    [SubstMap S S] [SubstMap S T]
    {r : Ren S} {τ : Subst S} (μ : Subst T)
    : (r ∘ τ) ◾ μ = r ∘ τ ◾ μ
  := by
    simp [hcompose, compose_ren_left, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite8_ren
    [RenMap S T] [SubstMap S S] [SubstMap S T]
    {r : Ren S} {τ : Subst S} (μ : Ren T)
    : (r ∘ τ) ◾ μ = r ∘ τ ◾ μ
  := by
    simp [hcompose_ren, compose_ren_left, act, SubstAction.act]

  @[simp, grind =]
  theorem hrewrite9
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
    {σ : Subst S} {r : Ren S} (μ : Subst T)
    : (σ ∘ r) ◾ μ = (σ ◾ μ) ∘ r
  := by
    simp [hcompose, compose_ren_right, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp
    rw [apply_commute_ren_subst]

  @[simp, grind =]
  theorem hrewrite9_ren
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
    {σ : Subst S} {r : Ren S} (μ : Ren T)
    : (σ ∘ r) ◾ μ = (σ ◾ μ) ∘ r
  := by
    simp [hcompose_ren, compose_ren_right, act, SubstAction.act]
    funext; case _ x =>
    generalize zdef : σ.inner x = z
    cases z <;> simp
    rw [apply_commute_ren_ren]

  theorem hrewrite_lift1
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
    {σ : Subst S} {τ : Subst T}
    : (σ ◾ τ).lift = σ.lift ◾ τ
  := by
    simp [lift, act, SubstAction.act]; congr; funext; case _ i =>
    cases i <;> simp [act, SubstAction.act]
    case _ n =>
      simp [hcompose, act, SubstAction.act]
      generalize zdef : σ.inner n = z
      cases z <;> simp; case _ t =>
      rw [apply_commute_ren_subst]

  @[simp, grind =]
  theorem hrewrite_lift
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T]
    [RenMapId S S] [RenMapCompose S S] [SubstMapRenCommute S T]
    {k} {σ : Subst S} {τ : Subst T}
    : (σ ◾ τ).lift k = σ.lift k ◾ τ
  := by
    induction k generalizing σ τ
    case _ => simp
    case _ i ih =>
      rw [rewrite_lift_succ]
      rw [rewrite_lift_succ]
      simp; rw [ih]
      grind

  theorem hrewrite_lift1_ren
    [RenMap S S] [SubstMap S S] [RenMap S T] [SubstMap S T] [SubstMapRenCommute S T]
    {σ : Subst S} {τ : Ren T}
    : (σ ◾ τ).lift = σ.lift ◾ τ
  := by
    simp [lift, act, SubstAction.act]; congr; funext; case _ i =>
    cases i <;> simp [act, SubstAction.act]
    case _ n =>
      simp [hcompose_ren, act, SubstAction.act]
      generalize zdef : σ.inner n = z
      cases z <;> simp; case _ t =>
      rw [apply_commute_ren_ren]

  @[simp, grind =]
  theorem hrewrite_lift_ren
    [RenMap S S] [RenMap S T] [SubstMap S S] [SubstMap S T]
    [RenMapId S S] [RenMapCompose S S] [SubstMapRenCommute S T]
    {k} {σ : Subst S} {τ : Ren T}
    : (σ ◾ τ).lift k = σ.lift k ◾ τ
  := by
    induction k generalizing σ τ
    case _ => simp
    case _ i ih =>
      rw [rewrite_lift_succ]
      rw [rewrite_lift_succ (k := i)]
      simp; rw [ih]
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
  simp [compose_ren_left, lift, Ren.lift, act, SubstAction.act]
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
  simp [lift, act, SubstAction.act]; congr; funext; case _ x =>
  cases x <;> simp [act, SubstAction.act]; case _ x =>
  simp [compose_ren_right, act, SubstAction.act]; grind

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
  [RenMap T T] [SubstMap T T] [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T T]
  {σ τ : Subst T}
  : (σ ∘ τ).lift = σ.lift ∘ τ.lift
:= by
  simp [compose, lift, act, SubstAction.act]
  funext; case _ x =>
  cases x <;> simp [act, SubstAction.act]
  case _ x =>
  cases σ.inner x <;> simp [act, SubstAction.act]; case _ t =>
  have lem := Subst.compose_commute_succ (τ := τ)
  simp [lift, act, SubstAction.act] at lem
  rw [lem]

@[simp, grind =]
theorem Subst.rewrite_lift_compose
  [RenMap T T] [RenMapId T T] [RenMapCompose T T] [SubstMap T T]
  [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T T]
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
  all_goals simp [*] at *; try simp +instances [*]
  all_goals try solve | rw [Subst.apply_stable h]
  all_goals try solve | (rw [<-h]; simp +instances [Ren.to])
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
