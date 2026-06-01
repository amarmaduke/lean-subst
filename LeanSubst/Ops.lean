
import LeanSubst.Types

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2}

----------------------------------------------------------------------------------------------------
---- Translation
----------------------------------------------------------------------------------------------------
def Ren.het T (r : Ren) : HetRen T := ⟨r.act⟩

@[simp]
theorem Ren.het_act {r : Ren} {x} : (r.het T).act x = r.act x := by simp [Ren.het]

def HetRen.forget (r : HetRen T) : Ren := ⟨r.act⟩

@[simp]
theorem HetRen.forget_act {r : HetRen T} {x} : r.forget.act x = r.act x := by simp [HetRen.forget]

@[simp]
theorem Ren.het_forget (r : Ren) : (r.het T).forget = r := by simp [Ren.het, HetRen.forget]

@[simp]
theorem HetRen.forget_het (r : HetRen T) : r.forget.het T = r := by simp [Ren.het, HetRen.forget]

def Subst.het S (σ : Subst T) : HetSubst S T := ⟨σ.act⟩

@[simp]
theorem Subst.het_act {r : Subst T} {x} : (r.het S).act x = r.act x := by simp [Subst.het]

def HetSubst.forget (σ : HetSubst S T) : Subst T := ⟨σ.act⟩

@[simp]
theorem HetSubst.forget_act {r : HetSubst S T} {x} : r.forget.act x = r.act x := by
  simp [HetSubst.forget]

@[simp]
theorem Subst.het_forget (σ : Subst T) : (σ.het S).forget = σ := by
  simp [Subst.het, HetSubst.forget]

@[simp]
theorem HetSubst.forget_het (σ : HetSubst S T) : σ.forget.het S = σ := by
  simp [Subst.het, HetSubst.forget]

def Ren.to (r : Ren) : Subst S := ⟨λ x => re (r.act x)⟩

@[simp]
theorem Ren.to_act {r : Ren} {x} : (@Ren.to S r).act x = re (r.act x) := by simp [Ren.to]

def HetRen.to (r : HetRen T) : HetSubst S T := ⟨λ x => re (r.act x)⟩

@[simp]
theorem HetRen.to_act {r : HetRen T} {x} : (@HetRen.to S T r).act x = re (r.act x) := by
  simp [HetRen.to]
----------------------------------------------------------------------------------------------------
---- Action
----------------------------------------------------------------------------------------------------
@[simp]
def Action.rmap [RenMap S] (r : Ren) : Action S -> Action S
| re x => re $ r.act x
| su t => su t⟨r⟩

instance [RenMap S] : RenMap (Action S) where
  rmap := Action.rmap

@[simp]
theorem Action.rmap_re [RenMap S] {r : Ren} {x : Nat}
  : (@re S x)⟨r⟩ = re (r.act x)
:= by simp [RenMap.rmap]

@[simp]
theorem Action.rmap_su [RenMap S] {r : Ren} {t : S} : (su t)⟨r⟩ = su t⟨r⟩ := by simp [RenMap.rmap]

@[simp]
def Action.hsmap [SubstMap S] (σ : HetSubst (Action S) S) : Action S -> Action S
| re x => σ.act x
| su t => su t[σ.forget]

instance [SubstMap S] : HetSubstMap (Action S) S where
  hsmap := Action.hsmap

@[simp]
theorem Action.hsmap_re [SubstMap S] {σ : HetSubst (Action S) S} {x : Nat}
  : (@re S x)[σ] = σ.act x
:= by simp [HetSubstMap.hsmap]

@[simp]
theorem Action.hsmap_su [SubstMap S] {σ : HetSubst (Action S) S} {t : S}
  : (su t)[σ] = su t[σ.forget]
:= by simp [HetSubstMap.hsmap]
----------------------------------------------------------------------------------------------------
---- Identity
----------------------------------------------------------------------------------------------------
def Ren.id : Ren := ⟨λ x => x⟩

@[simp]
theorem Ren.id_action {x} : id.act x = x := by simp [Ren.id]

def HetRen.id T : HetRen T := ⟨λ x => x⟩

@[simp]
theorem HetRen.id_action {x} : (id T).act x = x := by simp [HetRen.id]

def Subst.id : Subst S := ⟨λ x => re x⟩
notation "+0" => Subst.id

@[simp]
theorem Subst.id_action {x} : (@id S).act x = re x := by simp [Subst.id]

def HetSubst.id T : HetSubst S T := ⟨λ x => re x⟩
macro "+0@" noWs T:term : term =>`(HetSubst.id $T)

@[simp]
theorem HetSubst.id_action {x} : (@id S T).act x = re x := by simp [HetSubst.id]
----------------------------------------------------------------------------------------------------
---- Successor
----------------------------------------------------------------------------------------------------
def Ren.succ : Ren := ⟨(· + 1)⟩

@[simp]
theorem Ren.succ_action {x} : succ.act x = x + 1 := by simp [Ren.succ]

def HetRen.succ T : HetRen T := ⟨(· + 1)⟩

@[simp]
theorem HetRen.succ_action {x} : (succ T).act x = x + 1 := by simp [HetRen.succ]

def Subst.succ : Subst S := ⟨λ x => re $ x + 1⟩
notation "+1" => Subst.succ

@[simp]
theorem Subst.succ_action {x} : (@succ S).act x = re (x + 1) := by simp [Subst.succ]

def HetSubst.succ T : HetSubst S T := ⟨λ x => re $ x + 1⟩
macro "+1@" noWs T:term : term =>`(HetSubst.succ $T)

@[simp]
theorem HetSubst.succ_action {x} : (@succ S T).act x = re (x + 1) := by simp [HetSubst.succ]
----------------------------------------------------------------------------------------------------
---- Predecessor
----------------------------------------------------------------------------------------------------
def Ren.pred : Ren := ⟨(· - 1)⟩

@[simp]
theorem Ren.pred_action {x} : pred.act x = x - 1 := by simp [Ren.pred]

def HetRen.pred T : HetRen T := ⟨(· - 1)⟩

@[simp]
theorem HetRen.pred_action {x} : (pred T).act x = x - 1 := by simp [HetRen.pred]

def Subst.pred : Subst S := ⟨λ x => re $ x - 1⟩
notation "-1" => Subst.pred

@[simp]
theorem Subst.pred_action {x} : (@pred S).act x = re (x - 1) := by simp [Subst.pred]

def HetSubst.pred : HetSubst S T := ⟨λ x => re $ x - 1⟩
macro "-1@" noWs T:term : term =>`(HetSubst.pred $T)

@[simp]
theorem HetSubst.pred_action {x} : (@pred S T).act x = re (x - 1) := by simp [HetSubst.pred]
----------------------------------------------------------------------------------------------------
---- Addition
----------------------------------------------------------------------------------------------------
def Ren.add (k : Nat) : Ren := ⟨(· + k)⟩

@[simp]
theorem Ren.add_action {k x} : (add k).act x = x + k := by simp [Ren.add]

@[simp]
theorem Ren.add_zero : add 0 = id := by simp [Ren.add, Ren.id]

@[simp]
theorem Ren.add_one : add 1 = succ := by simp [Ren.add, Ren.succ]

def HetRen.add T (k : Nat) : HetRen T := ⟨(· + k)⟩

@[simp]
theorem HetRen.add_action {k x} : (add T k).act x = x + k := by simp [HetRen.add]

@[simp]
theorem HetRen.add_zero : add T 0 = id T := by simp [HetRen.add, HetRen.id]

@[simp]
theorem HetRen.add_one : add T 1 = succ T := by simp [HetRen.add, HetRen.succ]

def Subst.add (k : Nat) : Subst S := ⟨λ x => re $ x + k⟩

@[simp]
theorem Subst.add_action {k x} : (@add S k).act x = re (x + k) := by simp [Subst.add]

@[simp]
theorem Subst.add_zero : @add S 0 = id := by simp [Subst.add, Subst.id]

@[simp]
theorem Subst.add_one : @add S 1 = succ := by simp [Subst.add, Subst.succ]

def HetSubst.add (k : Nat) : HetSubst S T := ⟨λ x => re $ x + k⟩

@[simp]
theorem HetSubst.add_action {k x} : (@add S T k).act x = re (x + k) := by simp [HetSubst.add]

@[simp]
theorem HetSubst.add_zero : @add S T 0 = id T := by simp [HetSubst.add, HetSubst.id]

@[simp]
theorem HetSubst.add_one : @add S T 1 = succ T := by simp [HetSubst.add, HetSubst.succ]
----------------------------------------------------------------------------------------------------
---- Subtraction
----------------------------------------------------------------------------------------------------
def Ren.sub (k : Nat) : Ren := ⟨(· - k)⟩

@[simp]
theorem Ren.sub_action {k x} : (sub k).act x = x - k := by simp [Ren.sub]

@[simp]
theorem Ren.sub_zero : sub 0 = id := by simp [Ren.sub, Ren.id]

@[simp]
theorem Ren.sub_one : sub 1 = pred := by simp [Ren.sub, Ren.pred]

def HetRen.sub T (k : Nat) : HetRen T := ⟨(· - k)⟩

@[simp]
theorem HetRen.sub_action {k x} : (sub T k).act x = x - k := by simp [HetRen.sub]

@[simp]
theorem HetRen.sub_zero : sub T 0 = id T := by simp [HetRen.sub, HetRen.id]

@[simp]
theorem HetRen.sub_one : sub T 1 = pred T := by simp [HetRen.sub, HetRen.pred]
----------------------------------------------------------------------------------------------------
---- Cons
----------------------------------------------------------------------------------------------------
def Ren.cons (a : Nat) (r : Ren) : Ren := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => r.act n
infixr:67 (name := Ren.cons_notation) " :: " => Ren.cons

@[simp]
theorem Ren.cons_action0 {a} {r : Ren} : (a::r).act 0 = a := by simp [Ren.cons]

@[simp]
theorem Ren.cons_action {a i} {r : Ren} : (a::r).act (i + 1) = r.act i := by simp [Ren.cons]

def HetRen.cons (a : Nat) (r : HetRen T) : HetRen T := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => r.act n
infixr:67 (name := HetRen.cons_notation) " :: " => HetRen.cons

@[simp]
theorem HetRen.cons_action0 {a} {r : HetRen T} : (a::r).act 0 = a := by simp [HetRen.cons]

@[simp]
theorem HetRen.cons_action {a i} {r : HetRen T} : (a::r).act (i + 1) = r.act i := by
  simp [HetRen.cons]

def Subst.cons (a : Action S) (r : Subst S) : Subst S := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => r.act n
infixr:67 (name := Subst.cons_notation) " :: " => Subst.cons

@[simp]
theorem Subst.cons_action0 {a} {r : Subst S} : (a::r).act 0 = a := by simp [Subst.cons]

@[simp]
theorem Subst.cons_action {a i} {r : Subst S} : (a::r).act (i + 1) = r.act i := by simp [Subst.cons]

def HetSubst.cons (a : Action T) (r : HetSubst S T) : HetSubst S T := .mk λ n =>
  match n with
  | 0 => a
  | n + 1 => r.act n
infixr:67 (name := HetSubst.cons_notation) " :: " => HetSubst.cons

@[simp]
theorem HetSubst.cons_action0 {a} {r : HetSubst S T} : (a::r).act 0 = a := by simp [HetSubst.cons]

@[simp]
theorem HetSubst.cons_action {a i} {r : HetSubst S T} : (a::r).act (i + 1) = r.act i := by
  simp [HetSubst.cons]
----------------------------------------------------------------------------------------------------
---- Append
----------------------------------------------------------------------------------------------------
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

@[simp, grind <-]
theorem Ren.append_action_ge {r : Ren} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

def HetRen.append : List Nat -> HetRen T -> HetRen T
| .nil, r => r
| .cons hd tl, r => hd::append tl r

instance : HAppend (List Nat) (HetRen T) (HetRen T) where
  hAppend := HetRen.append

@[simp]
theorem HetRen.append_nil {r : HetRen T} : ([] : List Nat) ++ r = r := by
  simp [HAppend.hAppend, HetRen.append]

@[simp]
theorem HetRen.append_cons {a} {ℓ : List Nat} {r : HetRen T} : (a::ℓ) ++ r = a::(ℓ ++ r) := by
  simp [HAppend.hAppend, HetRen.append]

@[simp, grind <-]
theorem HetRen.append_action_lt {r : HetRen T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem HetRen.append_action_ge {r : HetRen T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

def Subst.append : List (Action S) -> Subst S -> Subst S
| .nil, r => r
| .cons hd tl, r => hd::append tl r

instance : HAppend (List $ Action S) (Subst S) (Subst S) where
  hAppend := Subst.append

@[simp]
theorem Subst.append_nil {r : Subst S} : ([] : List $ Action S) ++ r = r := by
  simp [HAppend.hAppend, Subst.append]

@[simp]
theorem Subst.append_cons {a} {ℓ : List $ Action S} {r : Subst S} : (a::ℓ) ++ r = a::(ℓ ++ r) := by
  simp [HAppend.hAppend, Subst.append]

@[simp, grind <-]
theorem Subst.append_action_lt {r : Subst S} {i}
  : {ℓ : List $ Action S} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_action_ge {r : Subst S} {i}
  : {ℓ : List $ Action S} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

def HetSubst.append : List (Action T) -> HetSubst S T -> HetSubst S T
| .nil, r => r
| .cons hd tl, r => hd::append tl r

instance : HAppend (List $ Action T) (HetSubst S T) (HetSubst S T) where
  hAppend := HetSubst.append

@[simp]
theorem HetSubst.append_nil {r : HetSubst S T} : ([] : List $ Action T) ++ r = r := by
  simp [HAppend.hAppend, HetSubst.append]

@[simp]
theorem HetSubst.append_cons {a} {ℓ : List $ Action T} {r : HetSubst S T}
  : (a::ℓ) ++ r = a::(ℓ ++ r)
:= by simp [HAppend.hAppend, HetSubst.append]

@[simp, grind <-]
theorem HetSubst.append_action_lt {r : HetSubst S T} {i}
  : {ℓ : List $ Action T} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem HetSubst.append_action_ge {r : HetSubst S T} {i}
  : {ℓ : List $ Action T} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)
----------------------------------------------------------------------------------------------------
---- Composition
----------------------------------------------------------------------------------------------------
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

def HetRen.compose : HetRen T -> HetRen T -> HetRen T
| r1, r2 => .mk λ n => r2.act (r1.act n)
infixr:85 (name := HetRen.compose_notation) " ∘ " => HetRen.compose

@[simp]
theorem HetRen.compose_action {r1 r2 : HetRen T} {x} : (r1 ∘ r2).act x = r2.act (r1.act x) := by
  simp [HetRen.compose]

@[simp]
theorem HetRen.compose_id_left {r : HetRen T} : id T ∘ r = r := by
  simp [HetRen.compose, HetRen.id]

@[simp]
theorem HetRen.compose_id_right {r : HetRen T} : r ∘ id T = r := by
  simp [HetRen.compose, HetRen.id]

@[simp]
theorem HetRen.compose_assoc {r1 r2 r3 : HetRen T} : (r1 ∘ r2) ∘ r3 = r1 ∘ r2 ∘ r3 := by
  simp [HetRen.compose]

def Subst.compose [RenMap S] [SubstMap S] : Subst S -> Subst S -> Subst S
| σ, τ => .mk λ n => (σ.act n)[τ.het _]
infixr:85 (name := Subst.compose_notation) " ∘ " => Subst.compose

@[simp]
theorem Subst.compose_action [RenMap S] [SubstMap S] {σ τ : Subst S} {x}
  : (σ ∘ τ).act x = (σ.act x)[τ.het _]
:= by simp [Subst.compose]

def HetSubst.compose [HetRenMap S T] [HetSubstMap S T] : HetSubst S T -> HetSubst S T -> HetSubst S T
| σ, τ => .mk λ n => (σ.act n)[τ]
infixr:85 (name := Subst.compose_notation) " ∘ " => Subst.compose

@[simp]
theorem Subst.compose_action [RenMap S] [SubstMap S] {σ τ : Subst S} {x}
  : (σ ∘ τ).act x = (σ.act x)[τ.het _]
:= by simp [Subst.compose]
----------------------------------------------------------------------------------------------------
---- Lift
----------------------------------------------------------------------------------------------------
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

theorem Ren.lift_compose_k1 {r1 r2 : Ren} : (r1 ∘ r2).lift = r1.lift ∘ r2.lift := by
  simp [Ren.compose, Ren.lift]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Ren.lift_compose {k} {r1 r2 : Ren} : (r1 ∘ r2).lift k = r1.lift k ∘ r2.lift k := by
  induction k generalizing r1 r2; simp
  case _ k ih =>
    rw [lift_of_succ, ih]
    rw [lift_of_succ (r := r1)]
    rw [lift_of_succ (r := r2)]
    rw [lift_compose_k1]




end LeanSubst
