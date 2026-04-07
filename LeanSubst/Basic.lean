import Lilac

namespace LeanSubst
  universe u
  variable {S T : Type}

  def Ren := Sequ Nat

  def Ren.id : Ren := λ x => x

  def Ren.lift (r : Ren) (k : Nat := 1) : Ren
  | n => if n < k then n else r (n - k) + k

  class RenMap (T : Type) where
    rmap : Ren -> T -> T

  export RenMap (rmap)

  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  def Subst (T : Type) := Sequ $ Subst.Action T

  @[coe]
  def Ren.to : Ren -> Subst T
  | r, n => re (r n)

  instance : Coe Ren (Subst T) where
    coe := Ren.to

  class SubstMap (S T : Type) where
    smap : Subst T -> S -> S

  export SubstMap (smap)

  def Subst.lift [RenMap T] (σ : Subst T) (k : Nat := 1) : Subst T
  | n => if n < k then re n else
    match σ (n - k) with
    | su t => su (rmap (· + k) t)
    | re i => re (i + k)

  @[simp]
  abbrev smap1 [SubstMap S S] := smap (S := S) (T := S)

  def Subst.compose [RenMap T] [SubstMap T T] : Subst T -> Subst T -> Subst T
  | σ, τ, n =>
    match σ n with
    | su t => su (smap τ t)
    | re k => τ k

  def Subst.hcompose [RenMap T] [SubstMap S T] : Subst S -> Subst T -> Subst S
  | σ, τ, n =>
    match σ n with
    | su t => su (smap τ t)
    | re k => re k

  def Subst.id : Subst T := λ n => re n
  def Subst.succ : Subst T := λ n => re (n + 1)
  def Subst.pred : Subst T := λ n => re (n - 1)

  notation "+0" => Subst.id
  macro "+0@" noWs T:term : term =>`(@Subst.id $T)
  notation "+1" => Subst.succ
  macro "+1@" noWs T:term : term =>`(@Subst.succ $T)
  notation "-1" => Subst.pred
  macro "-1@" noWs T:term : term =>`(@Subst.pred $T)

  @[simp, grind =]
  theorem Subst.id_action {n} : (+0@T) n = re n := by simp [Subst.id]

  @[simp, grind =]
  theorem Subst.succ_action {n} : (+1@T) n = re (n + 1) := by simp [Subst.succ]

  @[simp, grind =]
  theorem Subst.pred_action {n} : (-1@T) n = re (n - 1) := by simp [Subst.pred]

  @[simp, grind =]
  theorem Ren.to_id : Ren.to (T := T) id = +0 := by
    unfold Ren.to; unfold Subst.id; simp [id]

  @[simp, grind =]
  theorem Ren.to_succ : Ren.to (T := T) (· + 1) = +1 := by
    unfold Ren.to; simp; unfold Subst.succ; simp

  @[simp, grind =]
  theorem Ren.to_pred : Ren.to (T := T) (· - 1) = -1 := by
    unfold Ren.to; simp; unfold Subst.pred; simp

  @[simp, grind =]
  theorem Ren.pred_succ [RenMap T] [SubstMap T T] : Subst.compose (T := T) +1 -1 = +0 := by
    unfold Subst.compose; simp
    unfold Subst.id; rfl

  @[simp, grind =]
  theorem Ren.lift_zero {r : Ren} : r.lift 0 = r := by
    unfold Ren.lift; funext; case _ i => grind

  @[grind =]
  theorem Ren.lift_succ {r : Ren} {k} : r.lift (k + 1) = (r.lift k).lift := by
    induction k; simp
    case _ n ih =>
      unfold Ren.lift; funext; case _ i =>
      simp; unfold Ren.lift at ih; simp at ih
      grind

  @[simp]
  theorem Red.id_action {x} : Ren.id x = x := by simp [Ren.id]

  @[simp]
  theorem Ren.lift_id : Ren.lift Ren.id = Ren.id := by
    funext; case _ x =>
    cases x <;> simp [lift, id]

  @[grind =]
  theorem Ren.to_lift [RenMap T] {r : Ren} {k} : (r.lift k).to = (@Ren.to T r).lift k := by
    funext; case _ x =>
    cases x
    case zero =>
      unfold Ren.to; unfold Ren.lift; simp
      unfold Subst.lift; grind
    case _ n =>
      generalize lhsdef : ((@Ren.to T (r.lift k))) (n + 1) = lhs
      generalize rhsdef : ((@Ren.to T r).lift k) (n + 1) = rhs
      unfold Ren.to at lhsdef; simp at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      simp [Ren.to] at rhsdef
      subst lhsdef; subst rhsdef; grind

  @[simp, grind =]
  theorem Ren.to_compose {r1 r2 : Ren} [RenMap T] [SubstMap T T]
    : Ren.to (T := T) (r2 ∘ r1) = Subst.compose r1 r2
  := by
    funext; case _ x =>
    cases x <;> simp [Ren.to, Subst.compose]

  macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)
  macro:max t:term noWs "[" σ:term "]" : term => `(smap1 $σ $t)
  macro:max t:term noWs "[" σ:term ":" T:term "]" : term => `(smap (T := $T) $σ $t)
  infixr:85 " ∘ " => Ren.compose
  infixr:85 " ∘ " => Subst.compose
  infixr:85 " ◾ " => Subst.hcompose

  @[app_unexpander rmap]
  def unexpandRenApply : Lean.PrettyPrinter.Unexpander
  | `($_ $r $t) => `($t⟨$r⟩)
  | _ => throw ()

  @[app_unexpander smap1]
  def unexpandSubstApply1 : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ])
  | _ => throw ()

  @[app_unexpander smap]
  def unexpandSubstApply : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ : _])
  | `($_ (T := $T) $σ $t) => `($t[$σ : $T])
  | _ => throw ()

  instance : HAndThen Ren Ren Ren where
    hAndThen f g := (g ()) ∘ f

  instance : HAndThen (Nat -> Nat) Ren Ren where
    hAndThen f g := (g ()) ∘ f

  instance : HAndThen Ren (Nat -> Nat) Ren where
    hAndThen f g := (g ()) ∘ f

  instance : HAndThen (Sequ Nat) Ren Ren where
    hAndThen f g := (g ()) ∘ f

  instance : HAndThen Ren (Sequ Nat) Ren where
    hAndThen f g := (g ()) ∘ f

  @[simp]
  theorem Ren.id_promote : (λ x => x) = id := by unfold Ren.id; simp

  @[simp]
  theorem Ren.post_compose_id_left {r : Ren} : id >> r = r := by
    simp [HAndThen.hAndThen]; unfold id; unfold Function.comp; simp

  @[simp]
  theorem Ren.post_compose_id_right {r : Ren} : r >> id = r := by
    simp [HAndThen.hAndThen]; unfold id; unfold Function.comp; simp

  @[simp]
  theorem Ren.post_compose_assoc {r1 r2 r3 : Ren} : (r1 >> r2) >> r3 = r1 >> r2 >> r3 := by
    simp [HAndThen.hAndThen]; unfold Function.comp; simp

  @[simp]
  theorem Ren.post_compose_action {r1 r2 : Ren} {x} : (r1 >> r2) x = r2 (r1 x) := by
    simp [HAndThen.hAndThen]

  theorem Ren.post_compose_lift_k1 {r1 r2 : Ren} : (r1 >> r2).lift = r1.lift >> r2.lift := by
    funext; case _ x =>
    cases x <;> simp [Ren.lift]

  @[simp]
  theorem Ren.post_compose_lift {k} {r1 r2 : Ren} : (r1 >> r2).lift k = r1.lift k >> r2.lift k := by
    induction k generalizing r1 r2; simp
    case _ k ih =>
      rw [lift_succ, ih]
      rw [lift_succ (r := r1)]
      rw [lift_succ (r := r2)]
      rw [post_compose_lift_k1]

end LeanSubst
