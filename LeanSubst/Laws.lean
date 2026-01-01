import LeanSubst.Basic

namespace LeanSubst
  universe u
  variable {S T : Type}

  class SubstMapId (S T : Type) [RenMap T] [SubstMap S T] where
    apply_id {t : S} : t[+0:T] = t

  class SubstMapStable (S : Type) [RenMap S] [SubstMap S S] where
    apply_stable (r : Ren) (σ : Subst S) : r = σ -> Ren.apply (T := S) r = Subst.apply σ

  export SubstMapStable (apply_stable)

  class SubstMapCompose (S T : Type) [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] where
    apply_compose {s : S} {σ τ : Subst T} : s[σ:T][τ:_] = s[σ ∘ τ:T]

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

  end Subst

  macro "solve_stable" S:term "," r:term "," σ:term : tactic => `(tactic| {
    intro h; simp [Ren.apply, Subst.apply]
    funext; case _ t =>
    induction t generalizing $r $σ
    all_goals simp [RenMap.rmap, SubstMap.smap, *] at *; try simp [*]
    any_goals solve | (
      rw [<-Ren.lift_eq_from_eq (S := $S) h])
    any_goals solve | (rw [<-h]; simp [Ren.to])
  })

  macro "solve_compose" Ty:term "," s:Lean.Parser.Tactic.elimTarget "," σ:term "," τ:term : tactic => `(tactic| {
    have lem1 (τ : Subst $Ty) : (Ren.to (· + 1)) ∘ τ.lift = τ ∘ (Ren.to (· + 1)) := by
      funext; case _ x =>
      cases x <;> simp
    have lem1s (τ : Subst $Ty) : +1 ∘ τ.lift = τ ∘ +1 := by
      funext; case _ x =>
      cases x <;> simp
    have lem2 {σ : Subst $Ty} {r} : (r ∘ σ).lift = (Ren.to r).lift ∘ σ.lift := by
      funext; case _ x =>
      cases x <;> simp
      case _ x => simp [Ren.to, Subst.succ, Subst.compose]
    have lem2s {σ : Subst $Ty} : (+1 ∘ σ).lift = +1.lift ∘ σ.lift := by rw [<-Ren.to_succ, lem2]
    have lem3 {σ : Subst $Ty} {r : Ren} {t} : t[r][σ] = t[r ∘ σ] := by
      induction t generalizing σ r
      any_goals solve | simp [*]
      any_goals solve | (
        simp [-Subst.rewrite_lift, *]
        rw [<-Ren.to_lift (S := $Ty)]; simp [*])
    have lem3s {σ : Subst $Ty} {t} : t[+1][σ] = t[+1 ∘ σ] := by rw [<-Ren.to_succ, lem3]
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
    have lem7 {τ : Subst $Ty} {t} {r : Ren} : t[τ][r] = t[τ ∘ r.to] := by
      induction t generalizing τ r
      any_goals solve | simp [*]
      any_goals solve | (
        simp [-Subst.rewrite_lift, *]
        rw [<-Ren.to_lift (S := $Ty)]; simp [*])
    have lem7s {τ : Subst $Ty} {t} : t[τ][+1] = t[τ ∘ +1] := by rw [<-Ren.to_succ, lem7]
    have lem8 {σ τ : Subst $Ty} : (σ ∘ +1) ∘ τ = σ ∘ +1 ∘ τ := by
      funext; case _ x =>
      unfold Subst.compose; simp
      cases σ x <;> simp at *
      rw [lem3s]; unfold Subst.compose; simp
    have lem9 {σ τ : Subst $Ty} : ((σ ∘ τ) ∘ +1) = σ ∘ τ ∘ +1 := by
      funext; case _ x =>
      unfold Subst.compose; simp
      cases σ x <;> simp at *
      rw [lem7s]; unfold Subst.compose; simp
    have lem10 {σ τ : Subst $Ty} : (σ ∘ τ).lift = σ.lift ∘ τ.lift := by
      funext; case _ x =>
      cases x <;> simp [*]
    induction $s generalizing $σ $τ
    any_goals solve | simp [*]
    try any_goals solve | (
      simp [-Subst.rewrite_lift, *]
      rw [<-Ren.to_lift]; simp [*])
  })

end LeanSubst
