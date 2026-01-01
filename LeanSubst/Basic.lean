
-- TODO:
-- Generalizing to vector substitutions is a matter of the following change:
-- `SubstMap S T` becomes `SubstMap n S (T n)` for `T : Nat -> Type`
-- would want to make sure that length 1 substitutions are still nice to work with

-- Scoped versus Unscoped, does not appear to be a natural way to generalize to have
-- one development that gives both, easiest method would be to maintain two copies
-- Scoped is the natural consequence of `Ren n m := Fin n -> Fin m`

namespace LeanSubst
  universe u
  variable {S T : Type}

  @[simp]
  def Sequence.cons {T : Type u} (x : T) (xs : Nat -> T) : Nat -> T
  | 0 => x
  | n + 1 => xs n

  infixr:55 "::" => Sequence.cons

  def Endo (T : Type) := T -> T

  abbrev Ren := Nat -> Nat

  def Ren.lift : Endo Ren
  | _, 0 => 0
  | r, n + 1 => r n + 1

  class RenMap (T : Type) where
    rmap : Endo Ren -> Ren -> T -> T

  def Ren.apply [RenMap T] (r : Ren) : T -> T := RenMap.rmap Ren.lift r

  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  abbrev Subst (T : Type) := Nat -> Subst.Action T

  @[coe]
  def Ren.to : Ren -> Subst T
  | r, n => re (r n)

  instance : Coe Ren (Subst T) where
    coe := Ren.to

  class SubstMap (S T : Type) where
    smap : Endo (Subst T) -> Subst T -> S -> S

  def Subst.lift [RenMap T] : Endo (Subst T)
  | _, 0 => re 0
  | σ, n + 1 =>
    match σ n with
    | su t => su (Ren.apply (· + 1) t)
    | re k => re (k + 1)

  def Subst.apply [RenMap T] [SubstMap S T] (σ : Subst T) : S -> S := SubstMap.smap Subst.lift σ

  def Subst.compose [RenMap T] [SubstMap T T] : Subst T -> Subst T -> Subst T
  | σ, τ, n =>
    match σ n with
    | su t => su (apply τ t)
    | re k => τ k

  def Subst.hcompose [RenMap T] [SubstMap S T] : Subst S -> Subst T -> Subst S
  | σ, τ, n =>
    match σ n with
    | su t => su (apply τ t)
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

  @[simp]
  theorem Subst.id_action {n} : (+0@T) n = re n := by simp [Subst.id]

  @[simp]
  theorem Subst.succ_action {n} : (+1@T) n = re (n + 1) := by simp [Subst.succ]

  @[simp]
  theorem Subst.pred_action {n} : (-1@T) n = re (n - 1) := by simp [Subst.pred]

  @[simp]
  theorem Ren.to_id : Ren.to (T := T) id = +0 := by
    unfold Ren.to; unfold Subst.id; simp

  @[simp]
  theorem Ren.to_succ : Ren.to (T := T) (· + 1) = +1 := by
    unfold Ren.to; simp; unfold Subst.succ; simp

  @[simp]
  theorem Ren.to_pred : Ren.to (T := T) (· - 1) = -1 := by
    unfold Ren.to; simp; unfold Subst.pred; simp

  @[simp]
  theorem Ren.pred_succ [RenMap T] [SubstMap T T] : Subst.compose (T := T) +1 -1 = +0 := by
    unfold Subst.compose; simp
    unfold Subst.id; rfl

  @[simp]
  theorem Ren.to_compose {r1 r2 : Ren} [RenMap T] [SubstMap T T]
    : Ren.to (T := T) (r2 ∘ r1) = Subst.compose r1 r2
  := by
    funext; case _ x =>
    cases x <;> simp [Ren.to, Subst.compose]

  abbrev the {T : Type} (_ : T) := T

  macro:max t:term noWs "[" σ:term "]" : term => `(Subst.apply (S := the $t) (T := the $t) $σ $t)
  macro:max t:term noWs "[" σ:term ":" T:term "]" : term => `(Subst.apply (T := $T) $σ $t)
  infixr:85 " ∘ " => Subst.compose
  infixr:85 " • " => Subst.hcompose

  @[app_unexpander Subst.apply]
  def unexpandSubstApply : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ])
  | `($_ (T := $T) $σ $t) => `($t[$σ : $T])
  | `($_ (S := the $_) (T := the $_) $σ $t) => `($t[$σ])
  | _ => throw ()

end LeanSubst
