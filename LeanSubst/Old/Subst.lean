import LeanSubst.Ren

namespace LeanSubst
  universe u
  variable {S T : Type}

  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  @[simp]
  def Subst.Action.rmap {T} [RenMap T] (r : Ren) : Subst.Action T -> Subst.Action T
  | re x => re $ r.act x
  | su t => su t⟨r⟩

  instance [RenMap T] : RenMap (Subst.Action T) where
    rmap := Subst.Action.rmap

  @[simp]
  theorem Subst.Action.rmap_re [RenMap T] {r} {x : Nat}
    : (@re T x)⟨r⟩ = re (r.act x)
  := by simp [RenMap.rmap]

  @[simp]
  theorem Subst.Action.rmap_su [RenMap T] {r} {t : T} : (su t)⟨r⟩ = su t⟨r⟩ := by
    simp [RenMap.rmap]

  instance [RenMap T] [RenMapId T] : RenMapId (Subst.Action T) where
    apply_id := by
      intro t; simp [RenMap.rmap]
      cases t <;> simp

  instance [RenMap T] [RenMapCompose T] : RenMapCompose (Subst.Action T) where
    apply_compose := by
      intro s r1 r2; simp [RenMap.rmap, Ren.compose]
      cases s <;> simp [Ren.compose]

  structure Subst (T : Type) where
    act : Nat -> Subst.Action T

  def Subst.id : Subst T := ⟨λ x => re x⟩
  notation "+0" => Subst.id

  @[simp]
  theorem Subst.id_action {x} : (@Subst.id T).act x = re x := by simp [Subst.id]

  def Subst.succ : Subst T := ⟨λ x => re $ x + 1⟩
  notation "+1" => Subst.succ

  @[simp]
  theorem Subst.succ_action {x} : (@Subst.succ T).act x = re (x + 1) := by simp [Subst.succ]

  def Subst.pred : Subst T := ⟨λ x => re $ x - 1⟩
  notation "-1" => Subst.pred

  @[simp]
  theorem Subst.pred_action {x} : (@Subst.pred T).act x = re (x - 1) := by simp [Subst.pred]

  def Subst.add (k : Nat) : Subst T := ⟨λ x => re $ x + k⟩

  @[simp]
  theorem Subst.add_action {k x} : (@Subst.add T k).act x = re (x + k) := by simp [Subst.add]

  @[simp]
  theorem Subst.add_zero : add 0 = @id T := by simp [Subst.add, Subst.id]

  @[simp]
  theorem Subst.add_one : add 1 = @succ T := by simp [Subst.add, Subst.succ]

  def Subst.sub (k : Nat) : Subst T := ⟨λ x => re $ x - k⟩

  @[simp]
  theorem Subst.sub_action {k x} : (@Subst.sub T k).act x = re (x - k) := by simp [Subst.sub]

  @[simp]
  theorem Subst.sub_zero : sub 0 = @id T := by simp [Subst.sub, Subst.id]

  @[simp]
  theorem Subst.sub_one : sub 1 = @pred T := by simp [Subst.sub, Subst.pred]

  def Subst.cons (a : Subst.Action T) (σ : Subst T) : Subst T := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => σ.act n

  infixr:67 (name := Subst.cons_notation) " :: " => Subst.cons

  @[simp]
  theorem Subst.cons_action0 {a} {σ : Subst T} : (a::σ).act 0 = a := by simp [Subst.cons]

  @[simp]
  theorem Subst.cons_action {a i} {σ : Subst T} : (a::σ).act (i + 1) = σ.act i := by
    simp [Subst.cons]

  def Subst.append : List (Subst.Action T) -> Subst T -> Subst T
  | .nil, σ => σ
  | .cons hd tl, σ => hd::append tl σ

  instance : HAppend (List $ Subst.Action T) (Subst T) (Subst T) where
    hAppend := Subst.append

  @[simp]
  theorem Subst.append_nil {σ : Subst T} : ([] : List $ Action T) ++ σ = σ := by
    simp [HAppend.hAppend, Subst.append]

  @[simp]
  theorem Subst.append_cons {a} {ℓ : List (Action T)} {σ : Subst T}
    : (a::ℓ) ++ σ = a::(ℓ ++ σ)
  := by simp [HAppend.hAppend, Subst.append]

  @[simp, grind <-]
  theorem Subst.append_action_lt {σ : Subst T} {i}
    : {ℓ : List $ Action T} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = ℓ[i]
  | .cons hd tl, h =>
    match i with
    | 0 => rfl
    | i + 1 => append_action_lt (σ := σ) (ℓ := tl) (by grind)

  @[simp, grind =]
  theorem Subst.append_action_ge {σ : Subst T} {i}
    : {ℓ : List $ Action T} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
  | .nil, h => by simp
  | .cons hd tl, h =>
    match i with
    | 0 => by simp at h
    | i + 1 => @append_action_ge σ i tl (by grind) |> cast (by simp)

  class SubstMap (S T : Type) where
    smap : Subst T -> S -> S

  export SubstMap (smap)

  macro:max t:term noWs "[" σ:term "]" : term => `(smap $σ $t)

  @[app_unexpander smap]
  def unexpandSubstApply : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ])
  | _ => throw ()

  def Subst.compose [RenMap T] [SubstMap T T] : Subst T -> Subst T -> Subst T
  | σ, τ => .mk λ n =>
    match σ.act n with
    | su t => su t[τ]
    | re k => τ.act k

  infixr:85 (name := Subst.compose_notation) " ∘ " => Subst.compose

  def Subst.lift [RenMap T] (σ : Subst T) (k : Nat := 1) : Subst T := .mk λ n =>
    if n < k then re n else (σ.act (n - k))⟨.add k⟩

  @[simp, grind <-]
  theorem Subst.lift_action_lt [RenMap T] {σ : Subst T} {k i} (h : i < k)
    : (lift σ k).act i = re i
  := by simp [Subst.lift]; grind

  @[simp, grind <-]
  theorem Subst.lift_action_ge [RenMap T] {σ : Subst T} {k i} (h : i ≥ k)
    : (lift σ k).act i = (σ.act (i - k))⟨.add k⟩
  := by simp [Subst.lift]; grind

  -- @[simp]
  -- theorem Subst.lift_of_zero [RenMap T] [RenMapId T] {σ : Subst T} : σ.lift 0 = σ := by
  --   unfold Subst.lift; congr; simp

  -- @[grind =]
  -- theorem Subst.lift_of_succ [RenMap T] [RenMapId T] {σ : Subst T} {k} : σ.lift (k + 1) = (σ.lift k).lift := by
  --   induction k; simp
  --   case _ n ih =>
  --     unfold Subst.lift; congr; funext; case _ i =>
  --     simp; unfold Subst.lift at ih; simp at ih
  --     grind

  -- @[simp]
  -- theorem Subst.lift_id {k} : Subst.lift Subst.id k = Subst.id := by
  --   simp [Subst.id, Subst.lift]; congr; funext; case _ x =>
  --   cases x <;> simp; omega

  @[coe]
  def Ren.to : Ren -> Subst T
  | r  => .mk λ n => re (r.act n)

  instance : Coe Ren (Subst T) where
    coe := Ren.to

  @[simp, grind =]
  theorem Ren.to_id : Ren.to (T := T) id = +0 := by simp [Ren.to, Subst.id, id]

  @[simp, grind =]
  theorem Ren.to_succ : Ren.to (T := T) succ = +1 := by simp [Ren.to, Subst.succ]

  @[simp, grind =]
  theorem Ren.to_pred : Ren.to (T := T) pred = -1 := by simp [Ren.to, Subst.pred]

  @[simp, grind =]
  theorem Ren.to_add {k} : Ren.to (T := T) (add k) = Subst.add k := by simp [Ren.to, Subst.add]

  @[simp, grind =]
  theorem Ren.to_sub {k} : Ren.to (T := T) (sub k) = Subst.sub k := by simp [Ren.to, Subst.sub]

  @[simp, grind =]
  theorem Ren.pred_succ [RenMap T] [SubstMap T T] : Subst.compose (T := T) +1 -1 = +0 := by
    simp [Subst.compose, Subst.id]

  @[simp, grind =]
  theorem Ren.to_lift [RenMap T] {r : Ren} {k} : (r.lift k).to = (@Ren.to T r).lift k := by
    cases r; simp [Ren.lift, Ren.to, Subst.lift]; case _ act =>
    funext; case _ x =>
    cases x
    case zero => grind
    case _ n => cases Nat.decLt (n + 1) k <;> simp [ite]

  @[simp, grind =]
  theorem Ren.to_compose {r1 r2 : Ren} [RenMap T] [SubstMap T T]
    : Ren.to (T := T) (r1 ∘ r2) = r1.to ∘ r2.to
  := by
    funext; case _ x =>
    cases x <;> simp [Ren.to, Subst.compose, Ren.compose]

  -- def Subst.hcompose [RenMap T] [SubstMap S T] : Subst S -> Subst T -> Subst S
  -- | σ, τ => .mk λ n =>
  --   match σ.act n with
  --   | su t => su (smap τ t)
  --   | re k => re k

  -- infixr:85 " ◾ " => Subst.hcompose

  -- macro "+0@" noWs T:term : term =>`(@Subst.id $T)
  -- macro "+1@" noWs T:term : term =>`(@Subst.succ $T)
  -- macro "-1@" noWs T:term : term =>`(@Subst.pred $T)

end LeanSubst
