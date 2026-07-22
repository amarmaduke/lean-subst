
import LeanSubst.Basic
import LeanSubst.Tuple
open Lilac

namespace LeanSubst

universe u
variable {S T U : Type u}
variable {n : Nat} {V : Vec (Type u) n}

----------------------------------------------------------------------------------------------------
---- Var
----------------------------------------------------------------------------------------------------
-- @[simp]
-- def Var.rmap1 [RenMap S #(Ren S)] (r : Ren S) (x : Var S) : Var S := r.act x

-- instance (priority := high) [RenMap S #(Ren S)] : RenMap (Var S) #(Ren S) where
--   rmap := Var.rmap1

-- @[simp]
-- def Var.rmap0 [RenMap S V] (_ : V) (x : Var S) : Var S := x

-- instance (priority := low) [RenMap S V] : RenMap (Var S) V where
--   rmap := Var.rmap0

-- @[simp]
-- def Var.smap [i : SubstMap S V] (σ : V) (x : Var S) : Action S :=
--   match i.self with
--   | some ⟨k, e⟩ => (Tuple.get σ k |> cast e).act x
--   | none => re x

-- @[simp]
-- def Var.smap1 [SubstMap S #(Subst S)] (σ : Subst S) (x : Var S) : Action S := smap (σ::#⟨⟩) x
----------------------------------------------------------------------------------------------------
---- Action
----------------------------------------------------------------------------------------------------
@[simp]
theorem Subst.act_inner {f : Nat -> Action T} {x} : Subst.act { inner := f } x = f x := by
  simp [act, SubstAction.act]

@[simp]
def Action.rmap1 [RenMap S #(Ren S)] (r : Ren S) : Action S -> Action S
| re x => re $ r.act x
| su t => su t⟨r⟩

instance (priority := high) [RenMap S #(Ren S)] : RenMap (Action S) #(Ren S) where
  rmap := Action.rmap1

@[simp]
theorem Action.rmap1_re [RenMap S #(Ren S)] {r : Ren S} {x : Var S} : (@re S x)⟨r⟩ = re (r.act x) := by
  simp [RenMap.rmap, Tuple.cons]

@[simp]
theorem Action.rmap1_su [RenMap S #(Ren S)] {r : Ren S} {t : S} : (su t)⟨r⟩ = su t⟨r⟩ := by
  simp [RenMap.rmap, Tuple.cons]

@[simp]
def Action.rmap0 [RenMap S V] (r : V) : Action S -> Action S
| re x => re x
| su t => su t⟨r,⟩

instance (priority := low) [RenMap S V] : RenMap (Action S) V where
  rmap := Action.rmap0

@[simp]
theorem Action.rmap0_re [RenMap S V] {r : V} {x : Var S} : (@re S x)⟨r,⟩ = re x := by
  simp [RenMap.rmap]

@[simp]
theorem Action.rmap0_su [RenMap S V] {r : V} {t : S} : (su t)⟨r,⟩ = su t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
def Action.smap1 [SubstMap S #(Subst S)] (σ : Subst S) : Action S -> Action S
| re x => σ.act x
| su t => su t[σ]

instance (priority := high) [SubstMap S #(Subst S)] : SubstMap (Action S) #(Subst S) where
  smap := Action.smap1

@[simp]
theorem Action.smap1_re [SubstMap S #(Subst S)] {σ : Subst S} {x : Var S} : (@re S x)[σ] = σ.act x := by
  simp [SubstMap.smap, Subst.act, SubstAction.act, Tuple.cons]

@[simp]
theorem Action.smap1_su [SubstMap S #(Subst S)] {σ : Subst S} {t : S} : (su t)[σ] = su t[σ] := by
  simp [SubstMap.smap, Tuple.cons]

@[simp]
def Action.smap0 [SubstMap S V] (σ : V) : Action S -> Action S
| re x => re x
| su t => su t[σ,]

instance (priority := low) [SubstMap S V] : SubstMap (Action S) V where
  smap := Action.smap0

@[simp]
theorem Action.smap0_re [SubstMap S V] {σ : V} {x : Var S} : (@re S x)[σ,] = re x := by
  simp [SubstMap.smap]

@[simp]
theorem Action.smap0_su [SubstMap S V] {σ : V} {t : S} : (su t)[σ,] = su t[σ,] := by
  simp [SubstMap.smap]
----------------------------------------------------------------------------------------------------
---- Identity
----------------------------------------------------------------------------------------------------
def Ren.id T : Ren T := ⟨λ x => x⟩
notation "+0r" => Ren.id _

@[simp]
theorem Ren.id_action {x} : (id T).act x = x := by simp [id]

def Subst.id T : Subst T := ⟨λ x => re x⟩
notation "+0σ" => Subst.id _

@[simp]
theorem Subst.id_action {x} : (id T).act x = re x := by simp [id, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Successor
----------------------------------------------------------------------------------------------------
def Ren.succ T : Ren T := ⟨(· + 1)⟩
notation "+1r" => Ren.succ _

@[simp]
theorem Ren.succ_action {x} : (succ T).act x = x + 1 := by simp [succ]

def Subst.succ T : Subst T := ⟨λ x => re $ x + 1⟩
notation "+1σ" => Subst.succ _

@[simp]
theorem Subst.succ_action {x} : (succ T).act x = re (x + 1) := by simp [succ, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Predecessor
----------------------------------------------------------------------------------------------------
def Ren.pred T : Ren T := ⟨(· - 1)⟩
notation "-1r" => Ren.pred _

@[simp]
theorem Ren.pred_action {x} : (pred T).act x = x - 1 := by simp [pred]

def Subst.pred T : Subst T := ⟨λ x => re $ x - 1⟩
notation "-1σ" => Subst.pred _

@[simp]
theorem Subst.pred_action {x} : (pred T).act x = re (x - 1) := by simp [pred, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Addition
----------------------------------------------------------------------------------------------------
def Ren.add T (k : Nat) : Ren T := ⟨(· + k)⟩
notation "+r" => Ren.add _

@[simp]
theorem Ren.add_action {k x} : (add T k).act x = x + k := by simp [Ren.add]

@[simp]
theorem Ren.add_zero : add T 0 = +0r := by simp [Ren.add, Ren.id]

@[simp]
theorem Ren.add_one : add T 1 = +1r := by simp [Ren.add, Ren.succ]

def Subst.add T (k : Nat) : Subst T := ⟨λ x => re $ x + k⟩
notation "+σ" => Subst.add _

@[simp]
theorem Subst.add_action {k x} : (add T k).act x = re (x + k) := by simp [add, act, SubstAction.act]

@[simp]
theorem Subst.add_zero : add T 0 = +0σ := by simp [add, id]

@[simp]
theorem Subst.add_one : add T 1 = +1σ := by simp [add, succ]
----------------------------------------------------------------------------------------------------
---- Subtraction
----------------------------------------------------------------------------------------------------
def Ren.sub T (k : Nat) : Ren T := ⟨(· - k)⟩
notation "-r" => Ren.sub _

@[simp]
theorem Ren.sub_action {k x} : (sub T k).act x = x - k := by simp [sub]

@[simp]
theorem Ren.sub_zero : sub T 0 = +0r := by simp [sub, id]

@[simp]
theorem Ren.sub_one : sub T 1 = -1r := by simp [sub, pred]

def Subst.sub T (k : Nat) : Subst T := ⟨λ x => re $ x - k⟩
notation "-σ" => Subst.sub _

@[simp]
theorem Subst.sub_action {k x} : (@sub T k).act x = re (x - k) := by
  simp [sub, act, SubstAction.act]

@[simp]
theorem Subst.sub_zero : sub T 0 = +0σ := by simp [sub, id]

@[simp]
theorem Subst.sub_one : sub T 1 = -1σ := by simp [sub, pred]

----------------------------------------------------------------------------------------------------
---- Cons
----------------------------------------------------------------------------------------------------
def Ren.cons (a : Nat) (r : Ren T) : Ren T := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => r.act n
infixr:67 (name := Ren.cons_notation) " :: " => Ren.cons

@[simp]
theorem Ren.cons_action0 {a} {r : Ren T} : (a::r).act 0 = a := by simp [cons]

@[simp]
theorem Ren.cons_action {a i} {r : Ren T} : (a::r).act (i + 1) = r.act i := by simp [cons]

def Subst.cons (a : Action T) (σ : Subst T) : Subst T := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => σ.act n
infixr:67 (name := Subst.cons_notation) " :: " => Subst.cons

@[simp]
theorem Subst.cons_action0 {a} {σ : Subst T} : (a::σ).act 0 = a := by
  simp [cons, act, SubstAction.act]

@[simp]
theorem Subst.cons_action {a i} {σ : Subst T} : (a::σ).act (i + 1) = σ.act i := by
  simp [cons, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Append
----------------------------------------------------------------------------------------------------
def Ren.append : List Nat -> Ren T -> Ren T
| .nil, r => r
| .cons hd tl, r => hd::append tl r

instance : HAppend (List Nat) (Ren T) (Ren T) where
  hAppend := Ren.append

@[simp]
theorem Ren.append_nil {r : Ren T} : ([] : List Nat) ++ r = r := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Ren.append_cons {a} {ℓ : List Nat} {r : Ren T} : (a::ℓ) ++ r = a::(ℓ ++ r) := by
  simp [HAppend.hAppend, append]

@[simp, grind <-]
theorem Ren.append_action_lt {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Ren.append_action_ge {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

def Subst.append : List (Action T) -> Subst T -> Subst T
| .nil, r => r
| .cons hd tl, r => hd::append tl r

instance : HAppend (List $ Action T) (Subst T) (Subst T) where
  hAppend := Subst.append

@[simp]
theorem Subst.append_nil {σ : Subst T} : ([] : List $ Action T) ++ σ = σ := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Subst.append_cons {a} {ℓ : List $ Action T} {σ : Subst T} : (a::ℓ) ++ σ = a::(ℓ ++ σ) := by
  simp [HAppend.hAppend, append]

@[simp, grind <-]
theorem Subst.append_action_lt {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_action_ge {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge σ i tl (by grind) |> cast (by simp)

def Subst.append_ren : List Nat -> Subst T -> Subst T
| .nil, r => r
| .cons hd tl, r => re hd::append_ren tl r

instance : HAppend (List Nat) (Subst T) (Subst T) where
  hAppend := Subst.append_ren

@[simp]
theorem Subst.append_ren_nil {σ : Subst T} : ([] : List $ Nat) ++ σ = σ := by
  simp [HAppend.hAppend, append_ren]

@[simp]
theorem Subst.append_ren_cons {a} {ℓ : List Nat} {σ : Subst T} : (a::ℓ) ++ σ = re a::(ℓ ++ σ) := by
  simp [HAppend.hAppend, append_ren]

@[simp, grind <-]
theorem Subst.append_ren_action_lt {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = re ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_ren_action_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_ren_action_ge {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_ren_action_ge σ i tl (by grind) |> cast (by simp)
----------------------------------------------------------------------------------------------------
---- Composition
----------------------------------------------------------------------------------------------------
def Ren.compose : Ren T -> Ren T -> Ren T
| r1, r2 => .mk λ n => r2.act (r1.act n)
infixr:85 " ∘ " => Ren.compose

@[simp]
theorem Ren.compose_action {r1 r2 : Ren T} {x} : (r1 ∘ r2).act x = r2.act (r1.act x) := by
  simp [compose]

@[simp]
theorem Ren.compose_id_left {r : Ren T} : +0r ∘ r = r := by simp [compose, id]

@[simp]
theorem Ren.compose_id_right {r : Ren T} : r ∘ +0r = r := by simp [compose, id]

@[simp]
theorem Ren.compose_assoc {r1 r2 r3 : Ren T} : (r1 ∘ r2) ∘ r3 = r1 ∘ r2 ∘ r3 := by simp [compose]

@[simp]
theorem Ren.compose_pred_succ : +1r ∘ -1r = id T := by simp [succ, pred, id, compose]

@[simp]
theorem Ren.compose_sub_add {k} : +r k ∘ -r k = id T := by simp [sub, add, id, compose]

@[grind =]
theorem Ren.compose_add_succ_right {k} : add T (k + 1) = +r k ∘ +1r := by
  simp [add, succ, compose]; grind

@[grind =]
theorem Ren.compose_add_succ_left {k} : add T (k + 1) = +1r ∘ +r k := by
  simp [add, succ, compose]; grind

def Subst.compose [SubstMap T #(Subst T)] : Subst T -> Subst T -> Subst T
| σ, τ => .mk λ n => (σ.act n)[τ]
infixr:85 (name := Subst.compose_notation) " ∘ " => Subst.compose

@[simp]
theorem Subst.compose_action [SubstMap T #(Subst T)] {σ τ : Subst T} {x : Var T}
  : (σ ∘ τ).act x = (σ.act x)[τ]
:= by simp [compose, act, SubstAction.act, Tuple.cons]

@[simp]
theorem Subst.compose_pred_succ [SubstMap T #(Subst T)] : succ T ∘ pred T = id T := by
  simp [succ, pred, id, compose, act, SubstAction.act]

@[simp]
theorem Subst.compose_sub_add [SubstMap T #(Subst T)] {k} : add T k ∘ sub T k = id T := by
  simp [sub, add, id, compose, act, SubstAction.act]

@[grind =]
theorem Subst.compose_add_succ_right [SubstMap T #(Subst T)] {k} : add T (k + 1) = add T k ∘ succ T := by
  simp [add, succ, compose, act, SubstAction.act]; grind

@[grind =]
theorem Subst.compose_add_succ_left [SubstMap T #(Subst T)] {k} : add T (k + 1) = succ T ∘ add T k := by
  simp [add, succ, compose, act, SubstAction.act]; grind

def Subst.compose_ren_left : Ren T -> Subst T -> Subst T
| r, τ => .mk λ n => τ.act (r.act n)
infixr:85 (name := Subst.compose_ren_left_notation) " ∘ " => Subst.compose_ren_left

@[simp]
theorem Subst.compose_ren_left_action {r : Ren T} {τ : Subst T} {x}
  : (r ∘ τ).act x = τ.act (r.act x)
:= by simp [compose_ren_left, act, SubstAction.act]

def Subst.compose_ren_right [RenMap T #(Ren T)] : Subst T -> Ren T -> Subst T
| σ, r => .mk λ n => (σ.act n)⟨r⟩
infixr:85 (name := Subst.compose_ren_right_notation) " ∘ " => Subst.compose_ren_right

@[simp]
theorem Subst.compose_ren_right_action [RenMap T #(Ren T)] {σ : Subst T} {r : Ren T} {x : Nat}
  : (σ ∘ r).act x = (σ.act x)⟨r⟩
:= by simp [compose_ren_right, act, SubstAction.act]

-- def Subst.hcompose [SubstMap S T] : Subst S -> Subst T -> Subst S
-- | σ, τ => .mk λ n => (σ.act n)[τ]
-- infixr:85 " ◾ " => Subst.hcompose

-- @[simp]
-- theorem Subst.hcompose_action [SubstMap S T] {σ : Subst S} {τ : Subst T} {x : Nat}
--   : (σ ◾ τ).act x = (σ.act x)[τ]
-- := by simp [hcompose, act, SubstAction.act]

-- def Subst.hcompose_ren [RenMap S T] : Subst S -> Ren T -> Subst S
-- | σ, r => .mk λ n => (σ.act n)⟨r⟩
-- infixr:85 " ◾ " => Subst.hcompose_ren

-- @[simp]
-- theorem Subst.hcompose_ren_action [RenMap S T] {σ : Subst S} {r : Ren T} {x : Nat}
--   : (σ ◾ r).act x = (σ.act x)⟨r⟩
-- := by simp [hcompose_ren, act, SubstAction.act]
--
----------------------------------------------------------------------------------------------------
---- Lift
----------------------------------------------------------------------------------------------------
def Ren.lift (r : Ren T) (k : Nat := 1) : Ren T := .mk λ n =>
  if n < k then n else r.act (n - k) + k

@[simp, grind <-]
theorem Ren.lift_action_lt {r : Ren T} {k i} (h : i < k) : (lift r k).act i = i := by
  simp [lift]; grind

@[simp, grind <-]
theorem Ren.lift_action_ge {r : Ren T} {k i} (h : i ≥ k) : (lift r k).act i = r.act (i - k) + k :=
  by simp [lift]; grind

@[simp]
theorem Ren.lift_of_zero {r : Ren T} : r.lift 0 = r := by
  unfold Ren.lift; congr

@[grind =]
theorem Ren.lift_of_succ {r : Ren T} {k} : r.lift (k + 1) = (r.lift k).lift := by
  induction k; simp
  case _ n ih =>
    unfold Ren.lift; congr; funext; case _ i =>
    simp; unfold Ren.lift at ih; simp at ih
    grind

@[simp]
theorem Ren.lift_id {k} : lift (id T) k = id T := by
  simp [id, lift]; congr; funext; case _ x =>
  cases x <;> simp; grind

theorem Ren.lift_compose1 {r1 r2 : Ren T} : (r1 ∘ r2).lift = r1.lift ∘ r2.lift := by
  simp [compose, lift]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Ren.lift_compose {k} {r1 r2 : Ren T} : (r1 ∘ r2).lift k = r1.lift k ∘ r2.lift k := by
  induction k generalizing r1 r2; simp
  case _ k ih =>
    rw [lift_of_succ, ih]
    rw [lift_of_succ (r := r1)]
    rw [lift_of_succ (r := r2)]
    rw [lift_compose1]

def Subst.lift [RenMap T #(Ren T)] (σ : Subst T) (k : Nat := 1) : Subst T := .mk λ n =>
  if n < k then re n else (σ.act (n - k))⟨Ren.add T k⟩

@[simp, grind <-]
theorem Subst.lift_action_lt [RenMap T #(Ren T)] {σ : Subst T} {k i} (h : i < k)
  : (lift σ k).act i = re i
:= by simp [lift, act, SubstAction.act]; grind

@[simp, grind <-]
theorem Subst.lift_action_ge [RenMap T #(Ren T)] {σ : Subst T} {k i} (h : i ≥ k)
  : (lift σ k).act i = (σ.act (i - k))⟨Ren.add T k⟩
:= by simp [lift, act, SubstAction.act]; grind
----------------------------------------------------------------------------------------------------
---- Action on variable list
----------------------------------------------------------------------------------------------------
def Subst.act_list (σ : Subst T) : (ℓ : List Nat) -> List (Action T)
| [] => []
| .cons x xs => σ.act x :: act_list σ xs

instance : SubstAction T (List Nat) (List (Action T)) where
  act := Subst.act_list

@[simp]
theorem Subst.act_list_nil {σ : Subst T} : σ.act ([] : List Nat) = [] := by
  simp [act_list, act, SubstAction.act]

@[simp]
theorem Subst.act_list_cons {σ : Subst T} {x} {ℓ : List Nat} : σ.act (x::ℓ) = σ.act x :: σ.act ℓ :=
  by simp [act_list, act, SubstAction.act]

@[simp]
theorem Subst.act_list_append {σ : Subst T} {x y : List Nat}
  : σ.act (x ++ y) = σ.act x ++ σ.act y
:= by induction x generalizing y <;> simp [*]
----------------------------------------------------------------------------------------------------
---- Promotion
----------------------------------------------------------------------------------------------------
def Ren.to (r : Ren T) : Subst T := ⟨λ x => re (r.act x)⟩

@[simp]
theorem Ren.to_act {r : Ren T} {x} : (@to T r).act x = re (r.act x) := by simp [to, Subst.act, SubstAction.act]

@[simp]
theorem Ren.to_id : (id T).to = .id T := by simp [to, id, Subst.id]

@[simp]
theorem Ren.to_succ : (succ T).to = .succ T := by simp [to, succ, Subst.succ]

@[simp]
theorem Ren.to_pred : (pred T).to = .pred T := by simp [to, pred, Subst.pred]

@[simp]
theorem Ren.to_add {k} : (add T k).to = .add T k := by simp [to, add, Subst.add]

@[simp]
theorem Ren.to_sub {k} : (sub T k).to = .sub T k := by simp [to, sub, Subst.sub]

@[simp]
theorem Ren.to_lift [RenMap T #(Ren T)] {r : Ren T} {k} : (r.lift k).to = (@to T r).lift k := by
  cases r; simp [to, lift, Subst.lift, Subst.act, SubstAction.act]; case _ act =>
  funext; case _ x =>
  cases x; grind
  case _ n => cases Nat.decLt (n + 1) k <;> simp [ite]

@[simp]
theorem Ren.to_compose [RenMap T #(Ren T)] [SubstMap T #(Subst T)] {r1 r2 : Ren T}
  : @to T (r1 ∘ r2) = r1.to ∘ r2.to
:= by
  funext; case _ x =>
  cases x <;> simp [to, compose, Subst.compose, Subst.act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Range
----------------------------------------------------------------------------------------------------
def Ren.range : Nat -> Nat -> List Nat
| _, 0 => []
| s, e + 1 => if s ≤ e then (range s e).concat e else []

infix:90 ".." => Ren.range

@[simp]
theorem Ren.range_same {n} : n..n = [] := by cases n <;> simp [range]

@[simp, grind =]
theorem Ren.range_ge_nil {s e} {h : s ≥ e} : s..e = [] := by
  cases e <;> simp [range]; omega

@[simp, grind =]
theorem Ren.range_lt_cons {s e} {h : s < e} : s..e = s::(s.succ..e) := by
  induction e
  case _ => cases h
  case _ n ih =>
    cases Nat.decLt s n
    case _ h2 =>
      cases Nat.decEq s n
      case _ h3 => exfalso; grind
      case _ h3 => subst h3; simp [range]
    case _ h2 =>
      simp [range]
      rw [ite_cond_eq_true, ite_cond_eq_true, ih (h := h2)]
      all_goals grind

end LeanSubst
