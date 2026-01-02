import LeanSubst.Basic

namespace LeanSubst
  universe u
  variable {S T : Type}

  class SubstMapId (S T : Type) [RenMap T] [SubstMap S T] where
    apply_id {t : S} : t[+0:T] = t

  class SubstMapStable (S : Type) [RenMap S] [SubstMap S S] where
    apply_stable (r : Ren) (σ : Subst S) : r = σ -> Ren.apply (T := S) r = Subst.apply σ

  class SubstMapCompose (S T : Type) [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] where
    apply_compose {s : S} {σ τ : Subst T} : s[σ:T][τ:_] = s[σ ∘ τ:T]

  class SubstMapRenCommute (S T : Type) [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] where
    apply_ren_commute {s : S} (r : Ren) (τ : Subst T) : s[r.to][τ:T] = s[τ:T][r.to]

  class SubstMapHetCompose (S T : Type) [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] where
    apply_hcompose {s : S} {σ : Subst S} {τ : Subst T} : s[σ][τ:T] = s[τ:T][σ ◾ τ]

  namespace Subst
    export SubstMapStable (apply_stable)
    export SubstMapRenCommute (apply_ren_commute)
  end Subst

  theorem Ren.to_lift [RenMap T] [SubstMap S T] {r : Ren} : r.lift.to = (@Ren.to T r).lift := by
    funext; case _ x =>
    cases x
    case zero =>
      unfold Ren.to; unfold Ren.lift; simp
      unfold Subst.lift; simp
    case _ n =>
      generalize lhsdef : ((@Ren.to T r.lift)) (n + 1) = lhs
      generalize rhsdef : ((@Ren.to T r).lift) (n + 1) = rhs
      unfold Ren.to at lhsdef; simp at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      subst lhsdef; subst rhsdef; rfl

  theorem Ren.lift_eq_from_eq [RenMap T] [SubstMap S T] {r : Ren} {σ : Subst T}
    : r = σ -> r.lift = σ.lift
  := by intro h; rw [<-h, to_lift (S := S)]

  namespace Subst
    section
      @[simp]
      theorem rewrite1 : re 0 :: +1 = +0@T := by
        funext; case _ x =>
        cases x; all_goals (simp [Sequence.cons, Subst.id, Subst.succ])

      open SubstMap
      variable [RenMap T]

      @[simp]
      theorem I_lift : +0.lift = +0@T := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.lift, Subst.id])

      @[simp]
      theorem rewrite2 [SubstMap T T] {σ : Subst T} : +0 ∘ σ = σ := by
        funext; case _ x =>
        unfold Subst.compose; simp [Subst.id]

      @[simp]
      theorem rewrite3_replace [SubstMap T T] {σ τ : Subst T} {s : T}
        : (su s :: σ) ∘ τ = su s[τ] :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons])

      @[simp]
      theorem rewrite3_rename [SubstMap T T] {s} {σ τ : Subst T}
        : (re s :: σ) ∘ τ = (τ s) :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons])

      @[simp]
      theorem rewrite4 [SubstMap T T]  {s} {σ : Subst T} : +1 ∘ (s :: σ) = σ := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons, Subst.succ])

      @[simp]
      theorem rewrite5 [SubstMap T T] {σ : Subst T} : σ 0 :: (+1 ∘ σ) = σ := by
        funext; case _ x =>
        cases x
        case _ => simp
        case _ => simp [Subst.succ, Subst.compose]
    end

    @[simp]
    theorem apply_I_is_id [RenMap T] [SubstMap S T] [SubstMapId S T] {s : S}
      : s[+0:T] = s
    := SubstMapId.apply_id

    @[simp]
    theorem rewrite_lift [RenMap T] [SubstMap T T] [SubstMapStable T] {σ : Subst T}
      : σ.lift = re 0 :: (σ ∘ +1)
    := by
      funext; case _ x =>
      cases x
      case _ => simp [Subst.lift]
      case _ n =>
        simp [Subst.lift, Subst.succ, Subst.compose]
        generalize tdef : σ n = t
        cases t <;> simp at *
        case _ y =>
          rw [apply_stable (σ := +1)]
          funext; case _ i => simp [Ren.to, Subst.succ]

    @[simp]
    theorem rewrite6 [RenMap T] [SubstMap T T] [SubstMapId T T] {σ : Subst T}
      : σ ∘ +0 = σ
    := by
      funext; case _ x =>
      simp [Subst.compose, Subst.id, Subst.apply]
      generalize zdef : σ x = z
      cases z <;> simp at *; case _ t =>
      have lem := SubstMapId.apply_id (T := T) (t := t)
      simp [Subst.apply] at lem; exact lem

    @[simp]
    theorem apply_compose_commute
      [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
      {s : S} {σ τ : Subst T}
      : s[σ:T][τ:_] = s[σ ∘ τ:T]
    := SubstMapCompose.apply_compose

    @[simp]
    theorem rewrite7
      [RenMap T] [SubstMap T T] [SubstMapCompose T T]
      {σ τ μ : Subst T}
      : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ
    := by
      funext; case _ x =>
      simp [Subst.compose]
      cases σ x <;> simp

    @[simp]
    theorem hrewrite1
      [RenMap T] [SubstMap S T] [SubstMapId S T]
      {σ : Subst S}
      : σ ◾ (+0@T) = σ
    := by
      funext; case _ x =>
      simp [Subst.hcompose]
      generalize zdef : σ x = z
      cases z <;> simp

    @[simp]
    theorem hcomp_ren_left
      [RenMap S] [RenMap T] [SubstMap S T]
      (r : Ren) (σ : Subst T)
      : (@Ren.to S r) ◾ σ = r.to
    := by
      funext; case _ x =>
      induction x <;> simp [Subst.hcompose, Ren.to]

    @[simp]
    theorem hrewrite2
      [RenMap S] [RenMap T] [SubstMap S T]
      {σ : Subst T}
      : (+0@S) ◾ σ = +0
    := by
      apply hcomp_ren_left (S := S) (T := T) (λ x => x) σ

    @[simp]
    theorem hrewrite3
      [RenMap S] [RenMap T] [SubstMap S T]
      {σ : Subst T}
      : (+1@S) ◾ σ = +1
    := by
      have lem := hcomp_ren_left (S := S) (T := T) (· + 1) σ
      simp at lem; exact lem

    @[simp]
    theorem hrewrite4
      [RenMap T] [SubstMap S T]
      {x} {σ : Subst S} {τ : Subst T}
      : (re x :: σ) ◾ τ = re x :: (σ ◾ τ)
    := by
      funext; case _ i =>
      cases i <;> simp [Subst.hcompose]

    theorem hcomp_dist_ren_left
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
      (r : Ren) {σ : Subst S} {τ : Subst T}
      : (r.to ∘ σ) ◾ τ = r.to ∘ σ ◾ τ
    := by
      funext; case _ x =>
      simp [Subst.hcompose, Subst.compose, Ren.to]

    @[simp]
    theorem hrewrite5
      [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
      {σ : Subst S} {τ μ : Subst T}
      : (σ ◾ τ) ◾ μ = σ ◾ (τ ∘ μ)
    := by
      funext; case _ x =>
      simp [Subst.hcompose]
      generalize zdef : σ x = z
      cases z <;> simp

    theorem hcomp_distr_ren_right
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
      (r : Ren) (σ : Subst S) (μ : Subst T)
      : (σ ∘ r.to) ◾ μ = (σ ◾ μ) ∘ r.to
    := by
      funext; case _ x =>
      simp [Subst.hcompose, Subst.compose, Ren.to]
      generalize zdef : σ x = z
      cases z <;> simp
      rw [SubstMapRenCommute.apply_ren_commute r μ]

    @[simp]
    theorem hrewrite6
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapRenCommute S T]
      (r : Ren) (σ : Subst S)
      : (σ ∘ r.to) ◾ (+1@T) = (σ ◾ +1@T) ∘ r.to
    := by
      have lem := hcomp_distr_ren_right (T := T) r σ +1
      simp at lem; exact lem

    @[simp]
    theorem apply_hcompose
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
      {s : S} {σ : Subst S} {τ : Subst T}
      : s[σ][τ:T] = s[τ:T][σ ◾ τ]
    := by exact SubstMapHetCompose.apply_hcompose

    @[simp]
    theorem hrewrite7
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
      {σ τ : Subst S} (μ : Subst T)
      : (σ ∘ τ) ◾ μ = (σ ◾ μ) ∘ τ ◾ μ
    := by
      funext; case _ x =>
      simp [Subst.hcompose, Subst.compose]
      generalize zdef : σ x = z
      cases z <;> simp

    macro "solve_id" S:term "," T:term "," t:term : tactic => `(tactic| {
      have lem (t : $S) (r : Ren) : t[+0 ◾ (@Ren.to $T r):$S] = t := by
        induction t generalizing r <;> simp at *
        all_goals try simp [*]
      have h := lem $t id; simp at h; exact h
    })

    macro "solve_stable" S:term "," r:term "," σ:term : tactic => `(tactic| {
      intro h; simp [Ren.apply, Subst.apply]
      funext; case _ t =>
      induction t generalizing $r $σ
      all_goals simp [RenMap.rmap, SubstMap.smap, *] at *; try simp [*]
      any_goals solve | (
        rw [<-Ren.lift_eq_from_eq (S := $S) (r := $r) h])
      any_goals solve | (rw [<-h]; simp [Ren.to])
    })

    macro "solve_hcompose"
      S:term ","
      T:term ","
      s:Lean.Parser.Tactic.elimTarget ","
      σ:term ","
      τ:term
      : tactic =>
    `(tactic| {
      have lem1 {σ : Subst $S} {μ : Subst $T} {r : Ren} : (σ ∘ r.to) ◾ μ = (σ ◾ μ) ∘ r.to := by
        funext; case _ x =>
        simp [Subst.hcompose, Subst.compose]
        generalize zdef : σ x = z
        cases z <;> simp [Ren.to]
        rw [Subst.apply_ren_commute]
      have lem2 {σ : Subst $S} {μ : Subst $T} : (σ ∘ +1) ◾ μ = (σ ◾ μ) ∘ +1 := by
        have lem := @lem1 σ μ (· + 1)
        simp at lem; exact lem
      induction $s generalizing $σ $τ <;> simp at *
      all_goals simp [*]
    })

    macro "solve_compose"
      Ty:term ","
      s:Lean.Parser.Tactic.elimTarget ","
      σ:term ","
      τ:term
      : tactic =>
    `(tactic| {
      have lem1 (τ : Subst $Ty) : (Ren.to (· + 1)) ∘ τ.lift = τ ∘ (Ren.to (· + 1)) := by
        funext; case _ x =>
        cases x <;> simp
      have lem1s (τ : Subst $Ty) : +1 ∘ τ.lift = τ ∘ +1 := by
        funext; case _ x =>
        cases x <;> simp
      have lem2 {σ : Subst $Ty} {r} : (r ∘ σ).lift = (Ren.to r).lift ∘ σ.lift := by
        funext; case _ x =>
        cases x <;> simp
        try case _ x => simp [Ren.to, Subst.succ, Subst.compose]
      have lem2s {σ : Subst $Ty} : (+1 ∘ σ).lift = +1.lift ∘ σ.lift := by rw [<-Ren.to_succ, lem2]
      have lem3 {σ : Subst $Ty} {r : Ren} {t : $Ty} : t[r:$Ty][σ:_] = t[(r ∘ σ):_] := by
        induction t generalizing σ r
        any_goals solve | simp [*]
        try any_goals solve | (
          simp [-Subst.rewrite_lift, *]
          rw [<-Ren.to_lift (S := $Ty)]; simp [*])
      have lem3s {σ : Subst $Ty} {t : $Ty} : t[+1:$Ty][σ:_] = t[+1 ∘ σ:_] := by
        rw [<-Ren.to_succ, lem3]
      have lem4 {σ τ : Subst $Ty} : +1 ∘ τ ∘ σ = (+1 ∘ τ) ∘ σ := by
        funext; case _ x =>
        cases x <;> simp [Subst.compose, Subst.succ]
      have lem5 {r1 r2 : Ren} {τ : Subst $Ty} : (τ ∘ r2.to) ∘ r1.to = τ ∘ r2.to ∘ r1.to := by
        funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp [*]
        unfold Subst.compose; simp
      have lem6 {τ : Subst $Ty} {r : Ren} : (τ ∘ r.to).lift = τ.lift ∘ r.to.lift := by
        funext; case _ x =>
        cases x; simp
        case _ x =>
          simp [Subst.compose]
          cases τ x <;> simp [*]
      have lem6s {τ : Subst $Ty} : (τ ∘ +1).lift = τ.lift ∘ +1.lift := by rw [<-Ren.to_succ, lem6]
      have lem7 {τ : Subst $Ty} {t:$Ty} {r : Ren} : t[τ:_][r:$Ty] = t[τ ∘ r.to:_] := by
        induction t generalizing τ r
        any_goals solve | simp [*]
        try any_goals solve | (
          simp [-Subst.rewrite_lift, *]
          rw [<-Ren.to_lift (S := $Ty)]; simp [*])
      have lem7s {τ : Subst $Ty} {t : $Ty} : t[τ:_][+1:$Ty] = t[τ ∘ +1:_] := by
        rw [<-Ren.to_succ, lem7]
      have lem8 {σ τ : Subst $Ty} : (σ ∘ +1) ∘ τ = σ ∘ +1 ∘ τ := by
        funext; case _ x =>
        unfold Subst.compose; simp
        cases σ x <;> simp at *
        try rw [lem3s]
        unfold Subst.compose; simp
      have lem9 {σ τ : Subst $Ty} : ((σ ∘ τ) ∘ +1) = σ ∘ τ ∘ +1 := by
        funext; case _ x =>
        unfold Subst.compose; simp
        cases σ x <;> simp at *
        try rw [lem7s]
        unfold Subst.compose; simp
      have lem10 {σ τ : Subst $Ty} : (σ ∘ τ).lift = σ.lift ∘ τ.lift := by
        funext; case _ x =>
        cases x <;> simp [*]
      induction $s generalizing $σ $τ
      any_goals solve | simp [*]
      try any_goals solve | (
        simp [-Subst.rewrite_lift, *]
        rw [<-Ren.to_lift]; simp [*])
    })

  end Subst

end LeanSubst
