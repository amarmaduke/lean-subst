
namespace LeanSubst
  universe u
  variable {T : Type}

  @[simp]
  def Sequence.cons {T : Type u} (x : T) (xs : Nat -> T) : Nat -> T
  | 0 => x
  | n + 1 => xs n

  infixr:55 "::" => Sequence.cons

  abbrev Ren := Nat -> Nat

  inductive Subst.Kind : Type where
  | re | su

  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T

  abbrev Subst (T : Type) := Nat -> Subst.Action T

  def SplitSubst (T : Type) : Subst.Kind -> Type
  | .re => Ren
  | .su => Subst T

  abbrev Subst.Lift (T : Type) k := SplitSubst T k -> SplitSubst T k

  class SubstMap (T : Type) where
    smap : (k : Subst.Kind) -> Subst.Lift T k -> SplitSubst T k -> T -> T

  section
    variable [SubstMap T]

    open SubstMap

    @[coe]
    def Ren.to : Ren -> Subst T
    | r => λ n => .re (r n)

    @[simp]
    instance instCoe_Ren_Subst {T} : Coe Ren (Subst T) where
      coe := Ren.to

    def Ren.lift : Ren -> Ren
    | _, 0 => 0
    | σ, n + 1 => σ n + 1

    def Ren.apply (r : Ren) : T -> T := smap .re lift r

    def Subst.lift : Subst T -> Subst T
    | _, 0 => .re 0
    | σ, n + 1 => match (σ n) with
      | .su t => .su (Ren.apply (λ n => n + 1) t)
      | .re k => .re (k + 1)

    def Subst.apply (σ : Subst T) : T -> T := smap .su lift σ

    def Subst.compose : Subst T -> Subst T -> Subst T
    | σ, τ, n => match (σ n) with
      | .su t => .su (apply τ t)
      | .re k => τ k
  end

  def Subst.id : Subst T := λ n => .re n
  def Subst.succ : Subst T := λ n => .re (n + 1)

  notation "+0" => Subst.id
  notation "+1" => Subst.succ

  theorem Subst.id_action {n} : @Subst.id T n = .re n := by simp [Subst.id]
  theorem Subst.succ_action {n} : @Subst.succ T n = .re (n + 1) := by simp [Subst.succ]

  @[simp]
  theorem Ren.to_id : Ren.to (T := T) id = +0 := by
    unfold Ren.to; unfold Subst.id; simp

  @[simp]
  theorem Ren.to_succ : Ren.to (T := T) (· + 1) = +1 := by
    unfold Ren.to; simp; unfold Subst.succ; simp

  @[simp]
  theorem Ren.to_compose {r1 r2 : Ren} [SubstMap T]
    : Ren.to (T := T) (r2 ∘ r1) = Subst.compose r1 r2
  := by
    funext; case _ x =>
    cases x <;> simp [Ren.to, Subst.compose]

  macro:max t:term noWs "[" σ:term "]" : term => `(Subst.apply $σ $t)
  infixr:85 " ∘ " => Subst.compose

  class SubstMapStable (T : Type) [SubstMap T] where
    apply_id {t : T} : t[+0] = t
    apply_stable (r : Ren) (σ : Subst T) : r = σ -> Ren.apply r = Subst.apply σ

  class SubstMapCompose (T : Type) [SubstMap T] where
    apply_compose {s : T} {σ τ : Subst T} : s[σ][τ] = s[σ ∘ τ]

  theorem Ren.to_lift [SubstMap T] {r : Ren} : r.lift.to = (@Ren.to T r).lift := by
    funext; case _ x =>
    cases x
    case zero =>
      unfold Ren.to; unfold Ren.lift; simp
      unfold Subst.lift; simp
    case _ n =>
      generalize lhsdef : ((@Ren.to T r.lift)) (n + 1) = lhs
      generalize rhsdef : ((@Ren.to T r).lift) (n + 1) = rhs
      unfold Ren.to at lhsdef; simp [Ren.to] at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      subst lhsdef; subst rhsdef; rfl

  theorem Ren.lift_eq_from_eq [SubstMap T] {r : Ren} {σ : Subst T} : r = σ -> r.lift = σ.lift := by
    intro h; rw [<-h, to_lift]

  namespace Subst
    section
      @[simp] -- 0.S = I
      theorem rewrite1 : .re 0 :: +1 = @Subst.id T := by
        funext; case _ x =>
        cases x; all_goals (simp [Sequence.cons, Subst.id, Subst.succ])

      variable [SubstMap T]
      open SubstMap

      @[simp]
      theorem I_lift : +0.lift = @Subst.id T := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.lift, Subst.id])

      @[simp] -- σ ◦ I = σ
      theorem rewrite2 {σ : Subst T} : +0 ∘ σ = σ := by
        funext; case _ x =>
        unfold Subst.compose; simp [Subst.id]

      @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
      theorem rewrite3_replace {σ τ : Subst T} {s : T}
        : (.su s :: σ) ∘ τ = .su s[τ] :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons])

      @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
      theorem rewrite3_rename {s} {σ τ : Subst T}
        : (.re s :: σ) ∘ τ = (τ s) :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons])

      @[simp] -- S ◦ (s.σ ) = σ
      theorem rewrite4 {s} {σ : Subst T} : +1 ∘ (s :: σ) = σ := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Sequence.cons, Subst.succ])

      @[simp] -- 0[σ ].(S ◦ σ ) = σ
      theorem rewrite5 {σ : Subst T} : σ 0 :: (+1 ∘ σ) = σ := by
        funext; case _ x =>
        cases x
        case _ => simp
        case _ => simp [Subst.succ, Subst.compose]

      variable [SubstMapStable T]
      open SubstMapStable

      @[simp]
      theorem apply_I_is_id {s : T} : s[+0] = s :=
        SubstMapStable.apply_id

      @[simp] -- ⇑σ = 0.(σ ◦ S)
      theorem rewrite_lift {σ : Subst T} : σ.lift = .re 0 :: (σ ∘ +1) := by
        funext; case _ x =>
        cases x
        case _ => simp [Subst.lift]
        case _ n =>
          simp [Subst.lift, Subst.succ, Subst.compose]
          generalize tdef : σ n = t
          cases t <;> simp at *
          case _ y =>
            rw [apply_stable]
            funext; case _ i => simp [Ren.to, Subst.succ]

      @[simp] -- I ◦ σ = σ
      theorem rewrite6 {σ : Subst T} : σ ∘ +0 = σ := by
        funext; case _ x =>
        simp [Subst.compose, Subst.id, Subst.apply]
        generalize zdef : σ x = z
        cases z <;> simp at *; case _ t =>
        have lem := apply_id (T := T) (t := t)
        simp [Subst.apply] at lem; exact lem
    end

    section
      variable [SubstMap T] [SubstMapCompose T]

      open SubstMap
      open SubstMapCompose

      @[simp]
      theorem apply_compose_commute {s : T} {σ τ} : s[σ][τ] = s[σ ∘ τ] :=
        SubstMapCompose.apply_compose

      @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
      theorem rewrite7 {σ τ μ : Subst T} : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ := by
        funext; case _ x =>
        simp [Subst.compose]
        cases σ x <;> simp
    end
  end Subst

  macro "solve_stable" r:term "," σ:term : tactic => `(tactic| {
    intro h; simp [Ren.apply, Subst.apply]
    funext; case _ t =>
    induction t generalizing $r $σ <;> simp [Ren.to] at *
    all_goals simp [SubstMap.smap, *] at *; try simp [*]
    any_goals solve | (
      rw [<-Ren.lift_eq_from_eq h]
      simp [Ren.to])
    any_goals solve | (rw [<-h]; simp)
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
        rw [<-Ren.to_lift]; simp [*])
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
        cases τ x <;> simp [Subst.succ, *]
    have lem6s {τ : Subst $Ty} : (τ ∘ +1).lift = τ.lift ∘ +1.lift := by rw [<-Ren.to_succ, lem6]
    have lem7 {τ : Subst $Ty} {t} {r : Ren} : t[τ][r] = t[τ ∘ r.to] := by
      induction t generalizing τ r
      any_goals solve | simp [*]
      any_goals solve | (
        simp [-Subst.rewrite_lift, *]
        rw [<-Ren.to_lift]; simp [*])
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
