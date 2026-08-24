
import LeanSubst.Basic

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

----------------------------------------------------------------------------------------------------
---- RenVec & SubstVec; Map & GetElem
----------------------------------------------------------------------------------------------------
@[ext]
theorem RenVec.empty_ext {a b : RenVec []} : a = b := by sorry

@[ext]
theorem SubstVec.empty_ext {a b : SubstVec []} : a = b := by sorry

inductive Subst.TupleMap (F : Type u2 -> Type u2) : List (Type u2) -> Type _ where
| nil : Subst.TupleMap F []
| cons {T Ts} : F T -> Subst.TupleMap F Ts -> Subst.TupleMap F (T::Ts)

syntax (name := «term𝐭[_,]») "𝐭[" withoutPosition(term,*,?) "]" : term
open Lean in
macro_rules
| `(𝐭[ $elems,* ]) => do
  let rec expand_tuple_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
    match i, skip with
    | 0,     _     => pure result
    | i + 1, true  => expand_tuple_lit i false result
    | i + 1, false =>
      expand_tuple_lit i true (<- ``(Subst.TupleMap.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
  let size := elems.elemsAndSeps.size
  expand_tuple_lit size (size % 2 == 0) (<- ``(Subst.TupleMap.nil))

@[simp]
def RenVec.map
  : {V : List (Type u2)} -> Subst.TupleMap (λ T => Ren T -> Ren T) V -> RenVec V -> RenVec V
| [], .nil, r => r
| .cons _ _, .cons f fs, (r, rs) => (f r, rs.map fs)

-- @[simp]
-- def SubstVec.map
--   : {V : List (Type u2)} -> Subst.TupleMap (λ T => Subst T -> Subst T) V -> SubstVec V -> SubstVec V
-- | [], .nil, r => r
-- | .cons _ _, .cons f fs, (σ, σs) => (f σ, σs.map fs)

@[simp]
def RenVec.get
  : {V : List (Type u2)} -> (A : Type u2) -> (n : Nat) ->
    (h : V[n]? = some A := by grind) ->
    RenVec V -> Ren A
| .cons _ _, _, 0, h, (σ, _) => σ |> cast (by grind)
| .cons _ _, A, n + 1, _, (_, σs) => σs.get A n

-- @[simp]
-- theorem RenVec.get1_0 {r : RenVec [T1]} : r.get 0 = r.1 := sorry

@[simp]
def SubstVec.get
  : {V : List (Type u2)} -> (A : Type u2) -> (n : Nat) ->
    (h : V[n]? = some A := by grind) ->
    SubstVec V -> Subst A
| .cons _ _, _, 0, h, (σ, _) => σ |> cast (by grind)
| .cons _ _, A, n + 1, _, (_, σs) => σs.get A n

@[simp]
def SubstVec.drop : {V : List (Type u2)} -> (n : Nat) -> SubstVec V -> SubstVec (V.drop' n)
| [], n, x => x |> cast (by simp)
| .cons _ _, 0, x => x |> cast (by simp)
| .cons _ _, n + 1, (_, σs) => σs.drop n

@[simp]
theorem SubstVec.drop_0 {σ : SubstVec V} : σ.drop 0 = σ := sorry

-- @[simp]
-- theorem SubstVec.get1_0 {r : SubstVec [T1]} : r.get 0 = r.1 := sorry
----------------------------------------------------------------------------------------------------
---- RenMapAll & SubstMapAll
----------------------------------------------------------------------------------------------------
set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenMap T [T] where
  rmap :=
    match i with
    | @RenMapAll.cons _ _ i _ _ _ => i.rmap

@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenMap T V where
  rmap :=
    match i with
    | @RenMapAll.cons _ _ _ i _ _ => i.rmap

@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenSuffix T V :=
  match i with
  | @RenMapAll.cons _ _ _ _ i _ => i

set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenMapAll V :=
  match i with
  | @RenMapAll.cons _ _ _ _ _ i => i

-- instance [i1 : RenMap T1 [T1]] [i2 : RenMap T2 [T2]] : RenMapAll [T1, T2] where
--   rmap := by
--     intro i; cases i using Fin.cases with
--     | zero => exact i1
--     | succ i =>
--       cases i using Fin.cases with
--       | zero => exact i2
--       | succ i => apply Fin.elim0 i

set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstMap T [T] where
  smap :=
    match i with
    | @SubstMapAll.cons _ _ i _ _ _ => i.smap

@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstMap T V where
  smap :=
    match i with
    | @SubstMapAll.cons _ _ _ i _ _ => i.smap

@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstSuffix T V :=
  match i with
  | @SubstMapAll.cons _ _ _ _ i _ => i

set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstMapAll V :=
  match i with
  | @SubstMapAll.cons _ _ _ _ _ i => i

instance : RenMap T [] where
  rmap _ := id

instance : RenSuffix T [] := ⟨⟩

@[simp]
theorem rmap_empty_vec {t : T} {r : RenVec []} : t⟨r,⟩ = t := by simp [RenMap.rmap]

instance : RenMapAll [] := .nil

instance : SubstMap T [] where
  smap _ := id

instance : SubstSuffix T [] := ⟨⟩

@[simp]
theorem smap_empty_vec {t : T} {σ : SubstVec []} : t[σ,] = t := by simp [SubstMap.smap]

instance : SubstMapAll [] := .nil

-- instance [i : SubstMap T [T]] : SubstMapAll [T] where
--   smap := λ 0 => i

-- instance [i1 : SubstMap T1 [T1]] [i2 : SubstMap T2 [T2]] : SubstMapAll [T1, T2] where
--   smap := by
--     intro i; cases i using Fin.cases with
--     | zero => exact i1
--     | succ i =>
--       cases i using Fin.cases with
--       | zero => exact i2
--       | succ i => apply Fin.elim0 i
----------------------------------------------------------------------------------------------------
---- Var
----------------------------------------------------------------------------------------------------
-- @[simp]
-- def Var.rmap1 [RenMap S [S]] (r : Ren S) (x : Var S) : Var S := r.act x

-- instance (priority := high) [RenMap S [S]] : RenMap (Var S) [S] where
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
-- def Var.smap1 [SubstMap S [S]] (σ : Subst S) (x : Var S) : Action S := smap (σ::#⟨⟩) x
----------------------------------------------------------------------------------------------------
---- Action
----------------------------------------------------------------------------------------------------
@[simp]
theorem Subst.act_inner {f : Nat -> Action T} {x} : Subst.act { inner := f } x = f x := by
  simp [act, SubstAction.act]

@[simp]
def Action.rmap1 [RenMap T (T::V)] (r : RenVec (T::V)) : Action T -> Action T
| re x => re $ r.1.act x
| su t => su t⟨r,⟩

instance [RenMap T (T::V)] : RenMap (Action T) (T::V) where
  rmap v := Action.rmap1 v

@[simp]
theorem Action.rmap1_re [RenMap T (T::V)] {r : RenVec (T::V)} {x : Var T}
  : (@re T x)⟨r,⟩ = re (r.1.act x)
:= by simp [RenMap.rmap]

@[simp]
theorem Action.rmap1_su [RenMap T (T::V)] {r : RenVec (T::V)} {t : T} : (su t)⟨r,⟩ = su t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
def Action.rmap0 [RenMap S V] (r : RenVec V) : Action S -> Action S
| re x => re x
| su t => su t⟨r,⟩

instance [RenMap S V] [RenSuffix S V] : RenMap (Action S) V where
  rmap := Action.rmap0

@[simp]
theorem Action.rmap0_re [RenMap S V] [RenSuffix S V] {r : RenVec V} {x : Var S}
  : (@re S x)⟨r,⟩ = re x
:= by simp [RenMap.rmap]

@[simp]
theorem Action.rmap0_su [RenMap S V] [RenSuffix S V] {r : RenVec V} {t : S}
  : (su t)⟨r,⟩ = su t⟨r,⟩
:= by simp [RenMap.rmap]

@[simp]
def Action.smap1 [SubstMap T (T::V)] (σ : SubstVec (T::V)) : Action T -> Action T
| re x => σ.1.act x
| su t => su t[σ,]

instance [SubstMap T (T::V)] : SubstMap (Action T) (T::V) where
  smap v := Action.smap1 v

@[simp]
theorem Action.smap1_re [SubstMap T (T::V)] {σ : SubstVec (T::V)} {x : Nat}
  : (@re T x)[σ,] = σ.1.act x
:= by simp [SubstMap.smap, Subst.act, SubstAction.act]

@[simp]
theorem Action.smap1_su [SubstMap T (T::V)] {σ : SubstVec (T::V)} {t : T}
  : (su t)[σ,] = su t[σ,]
:= by simp [SubstMap.smap]

@[simp]
def Action.smap0 [SubstMap S V] (σ : SubstVec V) : Action S -> Action S
| re x => re x
| su t => su t[σ,]

instance [SubstMap S V] [SubstSuffix S V] : SubstMap (Action S) V where
  smap := Action.smap0

@[simp]
theorem Action.smap0_re [SubstMap S V] [SubstSuffix S V] {σ : SubstVec V} {x : Var S}
  : (@re S x)[σ,] = re x
:= by simp [SubstMap.smap]

@[simp]
theorem Action.smap0_su [SubstMap S V] [SubstSuffix S V] {σ : SubstVec V} {t : S}
  : (su t)[σ,] = su t[σ,]
:= by simp [SubstMap.smap]
----------------------------------------------------------------------------------------------------
---- Subst
----------------------------------------------------------------------------------------------------
def Subst.rmap0 [RenMap T (T::V)] (r : RenVec (T::V)) (σ : Subst T) : Subst T :=
  ⟨λ n => (σ.act n)⟨r,⟩⟩

instance [RenMap T (T::V)] : RenMap (Subst T) (T::V) where
  rmap := Subst.rmap0

@[simp]
theorem Subst.rmap0_simp [RenMap T (T::V)] {r : RenVec (T::V)} {σ : Subst T} {n : Nat}
  : (σ.act n)⟨r,⟩ = σ⟨r,⟩.act n
:= by simp [RenMap.rmap, rmap0]

def Subst.rmap1 [RenMap S V] [RenSuffix S V] (r : RenVec V) (σ : Subst S) : Subst S :=
  ⟨λ n => (σ.act n)⟨r,⟩⟩

instance [RenMap S V] [RenSuffix S V] : RenMap (Subst S) V where
  rmap := Subst.rmap1

@[simp]
theorem Subst.rmap1_simp [RenMap S V] [RenSuffix S V] {r : RenVec V} {σ : Subst S} {n : Nat}
  : (σ.act n)⟨r,⟩ = σ⟨r,⟩.act n
:= by simp [RenMap.rmap, rmap1]

def Subst.smap0 [SubstMap T (T::V)] (τ : SubstVec (T::V)) (σ : Subst T) : Subst T :=
  ⟨λ n => (σ.act n)[τ,]⟩

instance [SubstMap T (T::V)] : SubstMap (Subst T) (T::V) where
  smap := Subst.smap0

@[simp]
theorem Subst.smap0_simp [SubstMap T (T::V)] {τ : SubstVec (T::V)} {σ : Subst T} {n : Nat}
  : (σ.act n)[τ,] = σ[τ,].act n
:= by simp [SubstMap.smap, smap0]

def Subst.smap1 [SubstMap S V] [SubstSuffix S V] (τ : SubstVec V) (σ : Subst S) : Subst S :=
  ⟨λ n => (σ.act n)[τ,]⟩

instance [SubstMap S V] [SubstSuffix S V] : SubstMap (Subst S) V where
  smap := Subst.smap1

@[simp]
theorem Subst.smap1_simp
  [SubstMap S V] [SubstSuffix S V]
  {τ : SubstVec V} {σ : Subst S} {n : Nat}
  : (σ.act n)[τ,] = σ[τ,].act n
:= by simp [SubstMap.smap, smap1]
----------------------------------------------------------------------------------------------------
---- Identity
----------------------------------------------------------------------------------------------------
def Ren.id T : Ren T := ⟨λ x => x⟩
notation "𝐫0" => Ren.id _
notation "𝐫0(" T ")" => Ren.id T

@[simp]
theorem Ren.id_action {x} : 𝐫0(T).act x = x := by simp [id]

@[reducible, simp]
def RenVec.id : (V : List (Type u2)) -> RenVec V
| [] => .nil
| .cons x xs => (.id x, id xs)

def Subst.id T : Subst T := ⟨λ x => re x⟩
notation "𝐬0" => Subst.id _
notation "𝐬0(" T ")" => Subst.id T

@[simp]
theorem Subst.id_action {x} : 𝐬0(T).act x = re x := by simp [id, act, SubstAction.act]

@[reducible, simp]
def SubstVec.id : (V : List (Type u2)) -> SubstVec V
| [] => .nil
| .cons x xs => (.id x, id xs)
----------------------------------------------------------------------------------------------------
---- Successor
----------------------------------------------------------------------------------------------------
def Ren.succ T : Ren T := ⟨(· + 1)⟩
notation "𝐫1" => Ren.succ _
notation "𝐫1(" T ")" => Ren.succ T

@[simp]
theorem Ren.succ_action {x} : 𝐫1(T).act x = x + 1 := by simp [succ]

def Subst.succ T : Subst T := ⟨λ x => re $ x + 1⟩
notation "𝐬1" => Subst.succ _
notation "𝐬1(" T ")" => Subst.succ T

@[simp]
theorem Subst.succ_action {x} : 𝐬1(T).act x = re (x + 1) := by simp [succ, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Predecessor
----------------------------------------------------------------------------------------------------
def Ren.pred T : Ren T := ⟨(· - 1)⟩

@[simp]
theorem Ren.pred_action {x} : (pred T).act x = x - 1 := by simp [pred]

def Subst.pred T : Subst T := ⟨λ x => re $ x - 1⟩

@[simp]
theorem Subst.pred_action {x} : (pred T).act x = re (x - 1) := by simp [pred, act, SubstAction.act]
----------------------------------------------------------------------------------------------------
---- Addition
----------------------------------------------------------------------------------------------------
def Ren.add T (k : Nat) : Ren T := ⟨(· + k)⟩

@[simp]
theorem Ren.add_action {k x} : (add T k).act x = x + k := by simp [Ren.add]

@[simp]
theorem Ren.add_zero : add T 0 = 𝐫0 := by simp [Ren.add, Ren.id]

@[simp]
theorem Ren.add_one : add T 1 = 𝐫1 := by simp [Ren.add, Ren.succ]

def Subst.add T (k : Nat) : Subst T := ⟨λ x => re $ x + k⟩

@[simp]
theorem Subst.add_action {k x} : (add T k).act x = re (x + k) := by simp [add, act, SubstAction.act]

@[simp]
theorem Subst.add_zero : add T 0 = 𝐬0 := by simp [add, id]

@[simp]
theorem Subst.add_one : add T 1 = 𝐬1 := by simp [add, succ]
----------------------------------------------------------------------------------------------------
---- Subtraction
----------------------------------------------------------------------------------------------------
def Ren.sub T (k : Nat) : Ren T := ⟨(· - k)⟩

@[simp]
theorem Ren.sub_action {k x} : (sub T k).act x = x - k := by simp [sub]

@[simp]
theorem Ren.sub_zero : sub T 0 = 𝐫0 := by simp [sub, id]

@[simp]
theorem Ren.sub_one : sub T 1 = pred _ := by simp [sub, pred]

def Subst.sub T (k : Nat) : Subst T := ⟨λ x => re $ x - k⟩

@[simp]
theorem Subst.sub_action {k x} : (@sub T k).act x = re (x - k) := by
  simp [sub, act, SubstAction.act]

@[simp]
theorem Subst.sub_zero : sub T 0 = 𝐬0 := by simp [sub, id]

@[simp]
theorem Subst.sub_one : sub T 1 = pred _ := by simp [sub, pred]

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

instance : AndThen (Ren T) where
  andThen r f := Ren.compose r (f ())

def RenVec.compose : {V : List (Type u2)} -> RenVec V -> RenVec V -> RenVec V
| [], _, _ => .nil
| .cons _ _, (v1, v1s), (v2, v2s) => (v1 >> v2, compose v1s v2s)

instance : AndThen (RenVec V) where
  andThen r f := RenVec.compose r (f ())

@[simp]
theorem RenVec.compose_proj1 {σ τ : RenVec (T::V)} : (σ >> τ).1 = σ.1 >> τ.1 := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_proj2 {σ τ : RenVec (T::V)} : (σ >> τ).2 = σ.2 >> τ.2 := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_get [RenMapAll V] {σ τ : RenVec V} {i} {h}
  : (σ >> τ).get T i h = σ.get T i h >> τ.get T i h
:= sorry

@[simp]
theorem Ren.compose_action {r1 r2 : Ren T} {x} : (r1 >> r2).act x = r2.act (r1.act x) := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_id_left {r : Ren T} : 𝐫0 >> r = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem Ren.compose_id_right {r : Ren T} : r >> 𝐫0 = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem Ren.compose_assoc {r1 r2 r3 : Ren T} : (r1 >> r2) >> r3 = r1 >> r2 >> r3 := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_pred_succ : 𝐫1 >> pred T = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, succ, pred, id, compose]

@[simp]
theorem Ren.compose_sub_add {k} : add T k >> sub T k = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, id, compose]

@[grind =]
theorem Ren.compose_add_succ_right {k} : add T (k + 1) = add T k >> 𝐫1 := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, succ, compose]; grind

@[grind =]
theorem Ren.compose_add_succ_left {k} : add T (k + 1) = 𝐫1 >> add T k := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, succ, compose]; grind

def Subst.compose [SubstMap T [T]] : Subst T -> Subst T -> Subst T
| σ, τ => .mk λ n => (σ.act n)[τ]

instance [SubstMap T [T]] : AndThen (Subst T) where
  andThen σ f := Subst.compose σ (f ())

def SubstVec.compose
  : {V : List (Type u2)} -> [SubstMapAll V] ->
    SubstVec V -> SubstVec V -> SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, (v1, v1s), (v2, v2s) => (v1[v2s,] >> v2, compose v1s v2s)

instance [SubstMapAll V] : AndThen (SubstVec V) where
  andThen σ f := SubstVec.compose σ (f ())

@[simp]
theorem SubstVec.compose_cons [SubstMapAll (T::V)] {σ τ : Subst T} {σs τs : SubstVec V} :
  HAndThen.hAndThen (α := SubstVec (T::V)) (β := SubstVec (T::V)) (γ := SubstVec (T::V))
    (σ, σs) (λ _ => (τ, τs)) = (σ[τs,] >> τ, σs >> τs)
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_action [SubstMap T [T]] {σ τ : Subst T} {x : Var T}
  : (σ >> τ).act x = (σ.act x)[τ]
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose, act, SubstAction.act]

@[simp]
theorem Subst.compose_pred_succ [SubstMap T [T]] : succ T >> pred T = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, succ, pred, id, compose, act, SubstAction.act]

@[simp]
theorem Subst.compose_sub_add [SubstMap T [T]] {k} : add T k >> sub T k = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, id, compose, act, SubstAction.act]

@[grind =]
theorem Subst.compose_add_succ_right [SubstMap T [T]] {k} : add T (k + 1) = add T k >> succ T := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, succ, compose, act, SubstAction.act]; grind

@[grind =]
theorem Subst.compose_add_succ_left [SubstMap T [T]] {k} : add T (k + 1) = succ T >> add T k := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, succ, compose, act, SubstAction.act]; grind

def Subst.compose_ren_left : Ren T -> Subst T -> Subst T
| r, τ => .mk λ n => τ.act (r.act n)

instance : HAndThen (Ren T) (Subst T) (Subst T) where
  hAndThen r f := Subst.compose_ren_left r (f ())

def SubstVec.compose_ren_left
  : {V : List (Type u2)} -> RenVec V -> SubstVec V -> SubstVec V
| [],  _, _ => .nil
| .cons _ _, (v1, v1s), (v2, v2s) => (v1 >> v2, compose_ren_left v1s v2s)

instance : HAndThen (RenVec V) (SubstVec V) (SubstVec V) where
  hAndThen r f := SubstVec.compose_ren_left r (f ())

@[simp]
theorem Subst.compose_ren_left_action {r : Ren T} {τ : Subst T} {x}
  : (r >> τ).act x = τ.act (r.act x)
:= by simp [HAndThen.hAndThen, compose_ren_left, act, SubstAction.act]

def Subst.compose_ren_right [RenMap T [T]] : Subst T -> Ren T -> Subst T
| σ, r => .mk λ n => (σ.act n)⟨r⟩

instance [RenMap T [T]] : HAndThen (Subst T) (Ren T) (Subst T) where
  hAndThen σ f := Subst.compose_ren_right σ (f ())

def SubstVec.compose_ren_right
  : {V : List (Type u2)} -> [RenMapAll V] ->
    SubstVec V -> RenVec V -> SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, (v1, v1s), (v2, v2s) => (v1⟨v2s,⟩ >> v2, compose_ren_right v1s v2s)

instance [RenMapAll V] : HAndThen (SubstVec V) (RenVec V) (SubstVec V) where
  hAndThen σ f := SubstVec.compose_ren_right σ (f ())

@[simp]
theorem Subst.compose_ren_right_action [RenMap T [T]] {σ : Subst T} {r : Ren T} {x : Nat}
  : (σ >> r).act x = (σ.act x)⟨r⟩
:= by simp [HAndThen.hAndThen, compose_ren_right, act, SubstAction.act]

-- set_option linter.unusedVariables false in
-- @[instance_reducible]
-- def RenMapAll.get (T : Type u2) :
--   ∀ (x : Nat) {V : List (Type u2)} (h : V[x]? = some T), RenMapAll V -> RenMap T [T]
-- | 0, .cons V Vs, h, .cons (i1 := i1) (i2 := i2) _ => i1 |> cast (by grind)
-- | x + 1, .cons V Vs, h, .cons (i1 := i1) (i2 := i2) i3 => i3.get T x (by grind)

-- set_option linter.unusedVariables false in
-- @[instance_reducible]
-- def SubstMapAll.get (T : Type u2) :
--   ∀ (x : Nat) {V : List (Type u2)} (h : V[x]? = some T), SubstMapAll V -> SubstMap T [T]
-- | 0, .cons V Vs, h, .cons (i1 := i1) (i2 := i2) _ => i1 |> cast (by grind)
-- | x + 1, .cons V Vs, h, .cons (i1 := i1) (i2 := i2) i3 => i3.get T x (by grind)

-- set_option linter.unusedVariables false in
-- @[instance_reducible]
-- def SubstMapAll.get_drop (T : Type u2) :
--   ∀ {V : List (Type u2)} (n : Nat) (h : V[n]? = some T), SubstMapAll V -> SubstMap T (V.drop' (n + 1))
-- | [], n, h, σs => by cases h
-- | .cons V Vs, 0, h, .cons (i1 := i1) (i2 := i2) i3 => i2 |> cast (by grind)
-- | .cons V Vs, n + 1, h, .cons (i1 := i1) (i2 := i2) i3 => i3.get_drop T n (by grind)

-- @[simp]
-- theorem SubstVec.compose_ren_left_get {r : RenVec V} {σ : SubstVec V} {i h}
--   : (r >> σ).get T i h = r.get T i h >> σ.get T i h
-- := sorry

-- @[simp]
-- theorem SubstVec.compose_ren_right_get [inst : RenMapAll V] {σ : SubstVec V} {r : RenVec V} {i h}
--   : (σ >> r).get T i h
--     = let : RenMap T [T] := inst.get T i h; σ.get T i h >> r.get T i h
-- := sorry

@[simp]
theorem SubstVec.compose_ren_left_proj1 {r : RenVec (T::V)} {τ : SubstVec (T::V)}
  : (r >> τ).1 = r.1 >> τ.1
:= by
  rcases r with ⟨r, rs⟩
  rcases τ with ⟨τ, τs⟩
  simp [HAndThen.hAndThen, compose_ren_left]

@[simp]
theorem SubstVec.compose_ren_left_proj2 {r : RenVec (T::V)} {τ : SubstVec (T::V)}
  : (r >> τ).2 = r.2 >> τ.2
:= by
  rcases r with ⟨r, rs⟩
  rcases τ with ⟨τ, τs⟩
  simp [HAndThen.hAndThen, compose_ren_left]

@[simp]
theorem SubstVec.compose_ren_right_proj1 [RenMapAll (T::V)] {σ : SubstVec (T::V)} {r : RenVec (T::V)}
  : (σ >> r).1 = σ.1⟨r.2,⟩ >> r.1
:= by
  rcases σ with ⟨σ, σs⟩
  rcases r with ⟨r, rs⟩
  simp [HAndThen.hAndThen, compose_ren_right]

@[simp]
theorem SubstVec.compose_ren_right_proj2 [RenMapAll (T::V)] {σ : SubstVec (T::V)} {r : RenVec (T::V)}
  : (σ >> r).2 = σ.2 >> r.2
:= by
  rcases σ with ⟨σ, σs⟩
  rcases r with ⟨r, rs⟩
  simp [HAndThen.hAndThen, compose_ren_right]

@[simp]
theorem SubstVec.compose_proj1 [SubstMapAll (T::V)] {σ τ : SubstVec (T::V)}
  : (σ >> τ).1 = σ.1[τ.2,] >> τ.1
:= by
  rcases σ with ⟨σ, σs⟩
  rcases τ with ⟨τ, τs⟩
  simp

@[simp]
theorem SubstVec.compose_proj2 [SubstMapAll (T::V)] {σ τ : SubstVec (T::V)}
  : (σ >> τ).2 = σ.2 >> τ.2
:= by
  rcases σ with ⟨σ, σs⟩
  rcases τ with ⟨τ, τs⟩
  simp

-- @[simp]
-- theorem SubstVec.compose_get
--   : ∀ {V : List (Type u2)} [inst : SubstMapAll V] {σ τ : SubstVec V} {i h},
--     (σ >> τ).get T i h =
--       let : SubstMap T [T] := inst.get T i h
--       let : SubstMap T (V.drop' (i + 1)) := inst.get_drop T i h
--       (σ.get T i h)[τ.drop (i + 1),] >> τ.get T i h
-- | [], .nil, σ, τ, 0, h => by cases h
-- | .cons V Vs, .cons (i1 := i1) (i2 := i2) i3, (σ, σs), (τ, τs), 0, h =>
--   have h' : V = T := by grind
--   by subst h'; simp
-- | .cons V Vs, .cons (i1 := i1) (i2 := i2) i3, (σ, σs), (τ, τs), i + 1, h =>
--   have h' : Vs[i]? = some T := by grind
--   compose_get (V := Vs) (h := h')

----------------------------------------------------------------------------------------------------
---- Lift
----------------------------------------------------------------------------------------------------
def Ren.lift (r : Ren T) (k : Nat := 1) : Ren T := .mk λ n =>
  if n < k then n else r.act (n - k) + k

@[simp]
def RenVec.lift : {V : List (Type u2)} -> RenVec V -> List Nat -> RenVec V
| [], _, _ => .nil
| .cons _ _, (t, ts), [] => (t, ts)
| .cons _ _, (t, ts), (.cons k ks) => (t.lift k, ts.lift ks)

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

theorem Ren.lift_compose1 {r1 r2 : Ren T} : (r1 >> r2).lift = r1.lift >> r2.lift := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, lift]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Ren.lift_compose {k} {r1 r2 : Ren T} : (r1 >> r2).lift k = r1.lift k >> r2.lift k := by
  induction k generalizing r1 r2; simp
  case _ k ih =>
    rw [lift_of_succ, ih]
    rw [lift_of_succ (r := r1)]
    rw [lift_of_succ (r := r2)]
    rw [lift_compose1]

@[simp]
theorem RenVec.lift_compose {k} {r1 r2 : RenVec V} : (r1 >> r2).lift k = r1.lift k >> r2.lift k := by
  sorry

@[simp]
theorem RenVec.lift_proj1 {r : RenVec (T::V)} {n k} : (r.lift (n::k)).1 = r.1.lift n := by
  rcases r with ⟨r, r'⟩; simp

@[simp]
theorem RenVec.lift_proj2 {r : RenVec (T::V)} {n k} : (r.lift (n::k)).2 = r.2.lift k := by
  rcases r with ⟨r, r'⟩; simp

def Subst.lift [RenMap T [T]] (σ : Subst T) (k : Nat := 1) : Subst T := .mk λ n =>
  if n < k then re n else (σ.act (n - k))⟨Ren.add T k⟩

@[simp]
def SubstVec.lift : {V : List (Type u2)} -> [RenMapAll V] -> SubstVec V -> List Nat -> SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, (t, ts), [] => (t, ts)
| .cons _ _, _, (t, ts), (.cons k ks) => (t.lift k, ts.lift ks)

@[simp, grind <-]
theorem Subst.lift_action_lt [RenMap T [T]] {σ : Subst T} {k i} (h : i < k)
  : (lift σ k).act i = re i
:= by simp [lift, act, SubstAction.act]; grind

@[simp, grind <-]
theorem Subst.lift_action_ge [RenMap T [T]] {σ : Subst T} {k i} (h : i ≥ k)
  : (lift σ k).act i = (σ.act (i - k))⟨Ren.add T k⟩
:= by simp [lift, act, SubstAction.act]; grind

@[simp]
theorem SubstVec.lift_proj1 [RenMapAll (T::V)] {σ : SubstVec (T::V)} {n k} : (σ.lift (n::k)).1 = σ.1.lift n := by
  rcases σ with ⟨σ, σ'⟩; simp

@[simp]
theorem SubstVec.lift_proj2 [RenMapAll (T::V)] {σ : SubstVec (T::V)} {n k} : (σ.lift (n::k)).2 = σ.2.lift k := by
  rcases σ with ⟨σ, σ'⟩; simp
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
theorem Ren.to_lift [RenMap T [T]] {r : Ren T} {k} : (r.lift k).to = (@to T r).lift k := by
  cases r; simp [to, lift, Subst.lift, Subst.act, SubstAction.act]; case _ act =>
  funext; case _ x =>
  cases x; grind
  case _ n => cases Nat.decLt (n + 1) k <;> simp [ite]

@[simp]
theorem Ren.to_compose [RenMap T [T]] [SubstMap T [T]] {r1 r2 : Ren T}
  : @to T (r1 >> r2) = r1.to >> r2.to
:= by
  simp [to, HAndThen.hAndThen, AndThen.andThen, compose, Subst.compose, Subst.act, SubstAction.act]

def RenVec.to : {V : List (Type u2)} -> (r : RenVec V) -> SubstVec V
| [], _ => .nil
| .cons _ _, (r, rs) => (r.to, rs.to)
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

----------------------------------------------------------------------------------------------------
---- SubstVec Map
----------------------------------------------------------------------------------------------------
inductive SubstVec.MapOps : List (Type u2) -> Type _ where
| nil : MapOps []
| ren
  {S : Type u2} {V : List (Type u2)} (T : List (Type u2))
  [RenMap S T] [RenSuffix S T] (r : RenVec T)
  : MapOps V -> MapOps (S::V)
| lift {S : Type u2} {V : List (Type u2)} [RenMap S [S]] (n : Nat) : MapOps V -> MapOps (S::V)

@[simp]
def SubstVec.MapOps.to : {V : List (Type u2)} -> MapOps V -> List Nat
| [], nil => []
| .cons _ _, ren _ _ ops => 0::ops.to
| .cons _ _, lift n ops => n::ops.to

@[simp]
def SubstVec.map : {V : List (Type u2)} -> MapOps V -> SubstVec V -> SubstVec V
| [], .nil, σs => σs
| .cons _ _, MapOps.ren _ r ops, (σ, σs) => (σ⟨r,⟩, σs.map ops)
| .cons _ _, MapOps.lift n ops, (σ, σs) => (σ.lift n, σs.map ops)

@[simp]
theorem SubstVec.map_ren_proj1
  {X} [RenMap T X] [RenSuffix T X] {f : MapOps V} {r : RenVec X} {σ : SubstVec (T::V)}
  : (σ.map (.ren X r f)).1 = σ.1⟨r,⟩
:= by rcases σ with ⟨σ, σs⟩; simp

@[simp]
theorem SubstVec.map_ren_proj2
  {X} [RenMap T X] [RenSuffix T X] {f : MapOps V} {r : RenVec X} {σ : SubstVec (T::V)}
  : (σ.map (.ren X r f)).2 = σ.2.map f
:= by rcases σ with ⟨σ, σs⟩; simp

@[simp]
theorem SubstVec.map_lift_proj1
  [RenMap T [T]] {f : MapOps V} {n : Nat} {σ : SubstVec (T::V)}
  : (σ.map (.lift n f)).1 = σ.1.lift n
:= by rcases σ with ⟨σ, σs⟩; simp

@[simp]
theorem SubstVec.map_lift_proj2
  [RenMap T [T]] {f : MapOps V} {n : Nat} {σ : SubstVec (T::V)}
  : (σ.map (.lift n f)).2 = σ.2.map f
:= by rcases σ with ⟨σ, σs⟩; simp

end LeanSubst
