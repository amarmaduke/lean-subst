
namespace LeanSubst

  namespace Sequence
    @[simp]
    def cons {T} (x : T) (xs : Nat -> T) : Nat -> T
    | 0 => x
    | n + 1 => xs n
  end Sequence

  infixr:55 "::" => Sequence.cons

  def Ren := Nat -> Nat

  namespace Subst
    inductive Action (T : Type u) where
    | re : Nat -> Action T
    | su : T -> Action T

    def Lift (X : Type u) := (Nat -> Action X) -> Nat -> Action X
  end Subst

  def Subst (T : Type u) := Nat -> Subst.Action T

  class SubstMap (T : Type u) where
    smap : Subst.Lift T -> (Nat -> Subst.Action T) -> T -> T

  section
    variable {T : Type u} [SubstMap T]

    open SubstMap

    namespace Ren
      def to : Ren -> Subst T
      | r, n => .re (r n)

      def fro : Subst T -> Ren
      | σ, n =>
        match σ n with
        | .su _ => 0
        | .re k => k

      def lift : Ren -> Ren
      | _, 0 => 0
      | σ, n + 1 => σ n + 1

      def apply (r : Ren) : T -> T := smap (to ∘ lift ∘ fro) (to r)
    end Ren

    namespace Subst
      def lift : Subst T -> Subst T
      | _, 0 => .re 0
      | σ, n + 1 => match (σ n) with
        | .su t => .su (Ren.apply (λ n => n + 1) t)
        | .re k => .re (k + 1)

      def apply (σ : Subst T) : T -> T := smap lift σ

      def compose : Subst T -> Subst T -> Subst T
      | σ, τ, n => match (σ n) with
        | .su t => .su (apply τ t)
        | .re k => τ k
    end Subst
  end

  def I : Subst T := λ n => .re n
  def S : Subst T := λ n => .re (n + 1)
  def Sn (k : Nat) : Subst T := λ n => .re (n + k)

  @[simp] theorem I_action : @I T n = .re n := by unfold I; simp
  @[simp] theorem S_action : @S T n = .re (n + 1) := by unfold S; simp
  @[simp] theorem Sn_action : @Sn T k n = .re (n + k) := by unfold Sn; simp

  @[simp]
  theorem to_I : Ren.to (λ x => x) = @I T := by
    unfold Ren.to; simp; unfold I; simp

  @[simp]
  theorem to_S : Ren.to (λ x => x + 1) = @S T := by
    unfold Ren.to; simp; unfold S; simp

  @[simp]
  theorem to_Sn : Ren.to (λ x => x + k) = @Sn T k := by
    unfold Ren.to; simp; unfold Sn; simp

  notation t "[" σ "]" => Subst.apply σ t
  infixr:65 " ∘ " => Subst.compose

  class SubstMapStable (T : Type u) [SubstMap T] where
    apply_id {t : T} : t[I] = t
    apply_stable {σ : Subst T} : r.to = σ -> Ren.apply r = Subst.apply σ

  class SubstMapCompose (T : Type u) [SubstMap T] where
    apply_compose {s : T} {σ τ : Subst T} : s[σ][τ] = s[σ ∘ τ]

  namespace Ren
    section
      variable {T : Type u} [SubstMap T]

      theorem lift_to_commute {r : Ren} : r.lift.to = (@Ren.to T r).lift := by
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
    end
  end Ren

  namespace Subst
    section
      variable {T : Type u}

      @[simp] -- 0.S = I
      theorem rewrite1 : .re 0 :: S = @I T := by
        funext; case _ x =>
        cases x; all_goals (unfold Sequence.cons; unfold S; unfold I; simp)

      variable [SubstMap T]
      open SubstMap

      @[simp]
      theorem I_lift : I.lift = @I T := by
        funext; case _ x =>
        cases x; all_goals (unfold Subst.lift; unfold I; simp)

      @[simp] -- σ ◦ I = σ
      theorem rewrite2 {σ : Subst T} : I ∘ σ = σ := by
        funext; case _ x =>
        unfold Subst.compose; unfold I; simp

      @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
      theorem rewrite3_replace {σ τ : Subst T} {s : T}
        : (.su s :: σ) ∘ τ = .su (s[τ]) :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (unfold Subst.compose; unfold Sequence.cons; simp)

      @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
      theorem rewrite3_rename {s} {σ τ : Subst T}
        : (.re s :: σ) ∘ τ = (τ s) :: (σ ∘ τ)
      := by
        funext; case _ x =>
        cases x; all_goals (unfold Subst.compose; unfold Sequence.cons; simp)

      @[simp] -- S ◦ (s.σ ) = σ
      theorem rewrite4 {s} {σ : Subst T} : S ∘ (s :: σ) = σ := by
        funext; case _ x =>
        cases x; all_goals (unfold Subst.compose; unfold Sequence.cons; unfold S; simp)

      @[simp] -- 0[σ ].(S ◦ σ ) = σ
      theorem rewrite5 {σ : Subst T} : σ 0 :: (S ∘ σ) = σ := by
        funext; case _ x =>
        cases x
        case _ => simp
        case _ => simp; unfold S; unfold Subst.compose; simp

      variable [SubstMapStable T]
      open SubstMapStable

      @[simp]
      theorem apply_I_is_id {s : T} : s[I] = s :=
        SubstMapStable.apply_id

      @[simp] -- ⇑σ = 0.(σ ◦ S)
      theorem rewrite6 {σ : Subst T} : σ.lift = .re 0 :: (σ ∘ S) := by
        funext; case _ x =>
        cases x
        case _ => unfold Subst.lift; simp
        case _ n =>
          simp; unfold Subst.lift; unfold S; unfold Subst.compose; simp
          generalize tdef : σ n = t
          cases t <;> simp at *
          case _ y =>
            rw [apply_stable]
            funext; case _ i => unfold Ren.to; simp

      @[simp] -- I ◦ σ = σ
      theorem rewrite7 {σ : Subst T} : σ ∘ I = σ := by
        funext; case _ x =>
        unfold Subst.compose; unfold I; unfold Subst.apply; simp
        generalize zdef : σ x = z
        cases z <;> simp at *
        have lem : smap Subst.lift (λ x => .re x) = @Subst.apply T _ I := by
          unfold Subst.apply; unfold I; simp
        rw [lem, apply_id]
    end

    section
      variable {T : Type u} [SubstMap T] [SubstMapCompose T]

      open SubstMap
      open SubstMapCompose

      @[simp]
      theorem apply_compose_commute {s : T} {σ τ} : s[σ][τ] = s[σ ∘ τ] :=
        SubstMapCompose.apply_compose

      @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
      theorem rewrite8 {σ τ μ : Subst T} : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ := by
        funext; case _ x =>
        unfold Subst.compose; simp
        cases σ x <;> simp
        . unfold Subst.compose; simp
    end
  end Subst

  macro "solve_stable" r:term "," σ:term : tactic => `(tactic| {
    intro h; funext; case _ x =>
    unfold Ren.apply; simp [SubstMap.smap] at *
    unfold Ren.to; simp
    induction x generalizing $r $σ <;> simp at *
    any_goals simp [*]
    case _ x => rw [<-h]; unfold Ren.to; simp
    all_goals
      rw [Subst.lift_to_commute, <-h]
      unfold Ren.fro; simp
  })

  macro "solve_compose" Ty:term "," s:Lean.Parser.Tactic.elimTarget "," σ:term "," τ:term : tactic => `(tactic| {
    have lem1 (τ : Subst $Ty) : (Ren.to (· + 1)) ∘ τ.lift = τ ∘ (Ren.to (· + 1)) := by
      funext; case _ x =>
      cases x <;> simp
    have lem1s (τ : Subst $Ty) : S ∘ τ.lift = τ ∘ S := by
      rw [<-to_S, lem1]
    have lem2 {σ : Subst $Ty} {r} : ((Ren.to r) ∘ σ).lift = (Ren.to r).lift ∘ σ.lift := by
      funext; case _ x =>
      cases x <;> simp
      case _ x =>
        simp [Ren.to, Subst.compose]
    have lem2s {σ : Subst $Ty} : (S ∘ σ).lift = S.lift ∘ σ.lift := by
      rw [<-to_S, lem2]
    have lem3 {σ : Subst $Ty} {r t} : t[Ren.to r][σ] = t[(Ren.to r) ∘ σ] := by
      induction t generalizing σ r
      all_goals simp [-Subst.rewrite1, *]
      all_goals try rw [<-Subst.lift_to_commute]; simp [*]
      all_goals try (
        simp [Subst.compose]
        split <;> simp [*]
      )
    have lem3s {σ : Subst $Ty} {t} : t[S][σ] = t[S ∘ σ] := by
      rw [<-to_S, lem3]
    have lem4 {σ τ : Subst $Ty} : S ∘ τ ∘ σ = (S ∘ τ) ∘ σ := by
      funext; case _ x =>
      cases x <;> simp [Subst.compose]
    have lem5 {r1 r2} {τ : Subst $Ty}
      : (τ ∘ (Ren.to r2)) ∘ Ren.to r1 = τ ∘ (Ren.to r2) ∘ Ren.to r1
    := by
      funext; case _ x =>
      unfold Subst.compose; simp
      cases τ x <;> simp [*]
      unfold Subst.compose; simp
    have lem6 {τ : Subst $Ty} {r} : (τ ∘ (Ren.to r)).lift = τ.lift ∘ (Ren.to r).lift := by
      funext; case _ x =>
      cases x; simp
      case _ x =>
        simp [Subst.compose]
        cases τ x <;> simp [*]
    have lem6s {τ : Subst $Ty} : (τ ∘ S).lift = τ.lift ∘ S.lift := by
      rw [<-to_S, lem6]
    have lem7 {τ : Subst $Ty} {t r} : t[τ][Ren.to r] = t[τ ∘ (Ren.to r)] := by
      induction t generalizing τ r
      all_goals simp [-Subst.rewrite1, *]
      all_goals try rw [<-Subst.lift_to_commute]; simp [*]
      all_goals try (
        simp [Subst.compose]
        split <;> simp [*]
      )
    have lem7s {τ : Subst $Ty} {t} : t[τ][S] = t[τ ∘ S] := by
      rw [<-to_S, lem7]
    have lem8 {σ τ : Subst $Ty} : (σ ∘ S) ∘ τ = σ ∘ S ∘ τ := by
      funext; case _ x =>
      unfold Subst.compose; simp
      cases σ x <;> simp at *
      rw [lem3s]; unfold Subst.compose; simp
    have lem9 {σ τ : Subst $Ty} : ((σ ∘ τ) ∘ S) = σ ∘ τ ∘ S := by
      funext; case _ x =>
      unfold Subst.compose; simp
      cases σ x <;> simp at *
      rw [lem7s]; unfold Subst.compose; simp
    have lem10 {σ τ : Subst $Ty} : (σ ∘ τ).lift = σ.lift ∘ τ.lift := by
      funext; case _ x =>
      cases x <;> simp [*]
    induction $s generalizing $σ $τ
    all_goals simp [-Subst.rewrite1, *]
    all_goals try rw [<-Subst.lift_to_commute]; simp [*]
    all_goals try (
      simp [Subst.compose]
      split <;> simp [*]
    )
  })

end LeanSubst
