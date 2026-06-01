
namespace LeanSubst
  universe u
  variable {S T : Type}

  structure Ren where
    act : Nat -> Nat

  def Ren.id : Ren := ⟨λ x => x⟩

  @[simp]
  theorem Ren.id_action {x} : id.act x = x := by simp [Ren.id]

  def Ren.succ : Ren := ⟨(· + 1)⟩

  @[simp]
  theorem Ren.succ_action {x} : succ.act x = x + 1 := by simp [Ren.succ]

  def Ren.pred : Ren := ⟨(· - 1)⟩

  @[simp]
  theorem Ren.pred_action {x} : pred.act x = x - 1 := by simp [Ren.pred]

  def Ren.add (k : Nat) : Ren := ⟨(· + k)⟩

  @[simp]
  theorem Ren.add_action {k x} : (add k).act x = x + k := by simp [Ren.add]

  @[simp]
  theorem Ren.add_zero : add 0 = id := by simp [Ren.add, Ren.id]

  @[simp]
  theorem Ren.add_one : add 1 = succ := by simp [Ren.add, Ren.succ]

  def Ren.sub (k : Nat) : Ren := ⟨(· - k)⟩

  @[simp]
  theorem Ren.sub_action {k x} : (sub k).act x = x - k := by simp [Ren.sub]

  @[simp]
  theorem Ren.sub_zero : sub 0 = id := by simp [Ren.sub, Ren.id]

  @[simp]
  theorem Ren.sub_one : sub 1 = pred := by simp [Ren.sub, Ren.pred]

  def Ren.cons (a : Nat) (r : Ren) : Ren := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => r.act n

  infixr:67 (name := Ren.cons_notation) " :: " => Ren.cons

  @[simp]
  theorem Ren.cons_action0 {a} {r : Ren} : (a::r).act 0 = a := by simp [Ren.cons]

  @[simp]
  theorem Ren.cons_action {a i} {r : Ren} : (a::r).act (i + 1) = r.act i := by simp [Ren.cons]

  def Ren.append : List Nat -> Ren -> Ren
  | .nil, r => r
  | .cons hd tl, r => hd::append tl r

  instance : HAppend (List Nat) Ren Ren where
    hAppend := Ren.append

  @[simp]
  theorem Ren.append_nil {r : Ren} : ([] : List Nat) ++ r = r := by
    simp [HAppend.hAppend, Ren.append]

  @[simp]
  theorem Ren.append_cons {a} {ℓ : List Nat} {r : Ren} : (a::ℓ) ++ r = a::(ℓ ++ r) := by
    simp [HAppend.hAppend, Ren.append]

  @[simp, grind <-]
  theorem Ren.append_action_lt {r : Ren} {i}
    : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
  | .cons hd tl, h =>
    match i with
    | 0 => rfl
    | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

  @[simp, grind =]
  theorem Ren.append_action_ge {r : Ren} {i}
    : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
  | .nil, h => by simp
  | .cons hd tl, h =>
    match i with
    | 0 => by simp at h
    | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

  def Ren.compose : Ren -> Ren -> Ren
  | r1, r2 => .mk λ n => r2.act (r1.act n)

  infixr:85 (name := Ren.compose_notation) " ∘ " => Ren.compose

  @[simp]
  theorem Ren.compose_action {r1 r2 : Ren} {x} : (r1 ∘ r2).act x = r2.act (r1.act x) := by
    simp [Ren.compose]

  @[simp]
  theorem Ren.compose_id_left {r : Ren} : id ∘ r = r := by
    simp [Ren.compose, Ren.id]

  @[simp]
  theorem Ren.compose_id_right {r : Ren} : r ∘ id = r := by
    simp [Ren.compose, Ren.id]

  @[simp]
  theorem Ren.compose_assoc {r1 r2 r3 : Ren} : (r1 ∘ r2) ∘ r3 = r1 ∘ r2 ∘ r3 := by
    simp [Ren.compose]

  def Ren.lift (r : Ren) (k : Nat := 1) : Ren := .mk λ n =>
    if n < k then n else r.act (n - k) + k

  @[simp, grind <-]
  theorem Ren.lift_action_lt {r k i} (h : i < k) : (lift r k).act i = i := by
    simp [Ren.lift]; grind

  @[simp, grind <-]
  theorem Ren.lift_action_ge {r k i} (h : i ≥ k) : (lift r k).act i = r.act (i - k) + k := by
    simp [Ren.lift]; grind

  @[simp]
  theorem Ren.lift_of_zero {r : Ren} : r.lift 0 = r := by
    unfold Ren.lift; congr

  @[grind =]
  theorem Ren.lift_of_succ {r : Ren} {k} : r.lift (k + 1) = (r.lift k).lift := by
    induction k; simp
    case _ n ih =>
      unfold Ren.lift; congr; funext; case _ i =>
      simp; unfold Ren.lift at ih; simp at ih
      grind

  @[simp]
  theorem Ren.lift_id {k} : Ren.lift Ren.id k = Ren.id := by
    simp [Ren.id, Ren.lift]; congr; funext; case _ x =>
    cases x <;> simp; omega

  theorem Ren.compose_lift_k1 {r1 r2 : Ren} : (r1 ∘ r2).lift = r1.lift ∘ r2.lift := by
    simp [Ren.compose, Ren.lift]
    funext; case _ x =>
    cases x <;> simp

  @[simp]
  theorem Ren.compose_lift {k} {r1 r2 : Ren} : (r1 ∘ r2).lift k = r1.lift k ∘ r2.lift k := by
    induction k generalizing r1 r2; simp
    case _ k ih =>
      rw [lift_of_succ, ih]
      rw [lift_of_succ (r := r1)]
      rw [lift_of_succ (r := r2)]
      rw [compose_lift_k1]

  class RenMap (T : Type) where
    rmap : Ren -> T -> T

  export RenMap (rmap)

  macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)

  @[app_unexpander rmap]
  def unexpandRenApply : Lean.PrettyPrinter.Unexpander
  | `($_ $r $t) => `($t⟨$r⟩)
  | _ => throw ()

  class RenMapId (S : Type) [RenMap S] where
    apply_id {t : S} : t⟨Ren.id⟩ = t

  class RenMapCompose (S : Type) [RenMap S] where
    apply_compose {s : S} {r1 r2 : Ren} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

  @[simp]
  theorem Ren.apply_id [RenMap T] [RenMapId T] {t : T} : t⟨id⟩ = t := RenMapId.apply_id

  @[simp, grind =]
  theorem Ren.apply_compose [RenMap T] [RenMapCompose T] {t : T} {r1 r2 : Ren}
    : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
  := RenMapCompose.apply_compose

end LeanSubst
