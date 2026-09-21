
namespace LeanSubst

universe u u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}
variable {V : List (Type u2)}

class AltCons (S : outParam $ Type u1) (T : Type u2) where
  altCons : S -> T -> T

infixr:67 (name := «_.:_») " .: " => AltCons.altCons

@[reducible]
def Subst.typeof {T : Type u2} (_ : T) : Type u2 := T

structure Ren (T : Type u2) : Type u2 where
  act : Nat -> Nat

inductive RenVec : List (Type u2) -> Type (u2 + 1)
| nil : RenVec []
| cons {T V : _} : Ren T -> RenVec V -> RenVec (T::V)

infixr:67 (name := RenVec.cons_notation) " .: " => RenVec.cons

class RenSuffix (S : Type u1) (V : List (Type u2)) where

class RenMap (S : Type u1) (V : List (Type u2)) where
  rmap : RenVec V -> S -> S

class inductive RenMapAll : List (Type u2) -> Sort _ where
| nil : RenMapAll []
| cons {V Vs} [RenMap V (V::Vs)] : RenMapAll Vs -> RenMapAll (V::Vs)

export RenMap (rmap)

macro:max (name := «term_⟨_,⟩») t:term noWs "⟨" r:term ",⟩" : term => `(rmap $r $t)

syntax:max (name := «term_⟨_,*⟩») term noWs "⟨" term,* "⟩" : term
open Lean in
macro_rules
| `($t⟨ $elems,* ⟩) => do
  let elems := elems.getElems
  let rec expand_rmap_lit (i : Nat) (result : TSyntax `term) : MacroM Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expand_rmap_lit i (<- `(RenVec.cons $(elems[i]!) $result))
  let ren <- expand_rmap_lit elems.size (<- `(RenVec.nil))
  let ren : TSyntax `term := TSyntax.mk ren
  `(rmap $ren $t)

syntax (name := «term·⟨_,*⟩») "·⟨" withoutPosition(term,*,?) "⟩" : term
open Lean in
macro_rules
| `(·⟨ $elems,* ⟩) => do
  let elems := elems.getElems
  let rec expand_renvec_lit (i : Nat) (result : TSyntax `term) : MacroM Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expand_renvec_lit i (<- `(RenVec.cons $(elems[i]!) $result))
  expand_renvec_lit elems.size (<- `(RenVec.nil))

@[app_unexpander RenVec.nil]
meta def RenVec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(·⟨⟩)

@[app_unexpander RenVec.cons]
meta def RenVec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(·⟨⟩)      => `(·⟨$x⟩)
  | `(·⟨$xs,*⟩) => `(·⟨$x, $xs,*⟩)
  | _          => throw ()
| _ => throw ()

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ ($r1, RenVec.nil) $t) => `($t⟨$r1⟩)
| `($_ ($r1, $r2, RenVec.nil) $t) => `($t⟨$r1, $r2⟩)
| `($_ ($r1, $r2, $r3, RenVec.nil) $t) => `($t⟨$r1, $r2, $r3⟩)
| `($_ $r $t) => `($t⟨$r,⟩)
| _ => throw ()

inductive Action (T : Type u2) where
| re : Nat -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

structure Subst (T : Type u2) where
  inner : Nat -> Action T

inductive SubstVec : List (Type u2) -> Type (u2 + 1)
| nil : SubstVec []
| cons {T V : _} : Subst T -> SubstVec V -> SubstVec (T::V)

infixr:67 (name := SubstVec.cons_notation) " .: " => SubstVec.cons

class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
  act (σ : Subst T) : A -> U

def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

instance : SubstAction T Nat (Action T) where
  act := Subst.inner

class SubstSuffix (S : Type u1) (V : List (Type u2)) where

class SubstMap (S : Type u1) (V : List (Type u2)) where
  smap : SubstVec V -> S -> S

class inductive SubstMapAll : List (Type u2) -> Sort _ where
| nil : SubstMapAll []
| cons {V Vs} [SubstMap V (V::Vs)] : SubstMapAll Vs -> SubstMapAll (V::Vs)

export SubstMap (smap)

macro:max (name := «term_[_,]») t:term noWs "[" σ:term ",]" : term => `(smap $σ $t)

syntax:max (name := «term_[_,*]») term noWs "[" term ,* "]" : term
open Lean in
macro_rules
| `($t[ $elems,* ]) => do
  let elems := elems.getElems
  let rec expand_smap_lit (i : Nat) (result : TSyntax `term) : MacroM Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expand_smap_lit i (<- `(SubstVec.cons $(elems[i]!) $result))
  let subst <- expand_smap_lit elems.size (<- `(SubstVec.nil))
  let subst : TSyntax `term := TSyntax.mk subst
  `(smap $subst $t)

syntax (name := «term·[_,*]») "·[" withoutPosition(term,*,?) "]" : term
open Lean in
macro_rules
| `(·[ $elems,* ]) => do
  let elems := elems.getElems
  let rec expand_substvec_lit (i : Nat) (result : TSyntax `term) : MacroM Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expand_substvec_lit i (<- `(SubstVec.cons $(elems[i]!) $result))
  expand_substvec_lit elems.size (<- `(SubstVec.nil))

@[app_unexpander SubstVec.nil]
meta def SubstVec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(·[])

@[app_unexpander SubstVec.cons]
meta def SubstVec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(·[])      => `(·[$x])
  | `(·[$xs,*]) => `(·[$x, $xs,*])
  | _          => throw ()
| _ => throw ()

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ ($σ1, SubstVec.nil) $t) => `($t[$σ1])
| `($_ ($σ1, $σ2, SubstVec.nil) $t) => `($t[$σ1, $σ2])
| `($_ ($σ1, $σ2, $σ3, SubstVec.nil) $t) => `($t[$σ1, $σ2, $σ3])
| `($_ $σ $t) => `($t[$σ,])
| _ => throw ()

@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenMap T (T::V) where
  rmap :=
    match i with
    | @RenMapAll.cons _ _ i _ => i.rmap

set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : RenMapAll (T::V)] : RenMapAll V :=
  match i with
  | @RenMapAll.cons _ _ _ i => i

@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstMap T (T::V) where
  smap :=
    match i with
    | @SubstMapAll.cons _ _ i _ => i.smap

set_option synthInstance.checkSynthOrder false in
@[reducible, simp]
instance [i : SubstMapAll (T::V)] : SubstMapAll V :=
  match i with
  | @SubstMapAll.cons _ _ _ i => i

def RenVec.head : RenVec (T::V) -> Ren T
| cons r _ => r

def RenVec.tail : RenVec (T::V) -> RenVec V
| cons _ r => r

@[simp]
theorem RenVec.head_cons {r : Ren T} {rs : RenVec V} : (r .: rs).head = r := by simp [head]

@[simp]
theorem RenVec.tail_cons {r : Ren T} {rs : RenVec V} : (r .: rs).tail = rs := by simp [tail]

def SubstVec.head : SubstVec (T::V) -> Subst T
| cons σ _ => σ

def SubstVec.tail : SubstVec (T::V) -> SubstVec V
| cons _ σ => σ

@[simp]
theorem SubstVec.head_cons {σ : Subst T} {σs : SubstVec V} : (σ .: σs).head = σ := by simp [head]

@[simp]
theorem SubstVec.tail_cons {σ : Subst T} {σs : SubstVec V} : (σ .: σs).tail = σs := by simp [tail]

@[simp]
theorem Subst.act_inner {f : Nat -> Action T} {x} : Subst.act { inner := f } x = f x := by
  simp [act, SubstAction.act]

@[simp]
def Action.rmap1 [RenMap T (T::V)] (r : RenVec (T::V)) : Action T -> Action T
| re x => re $ r.head.act x
| su t => su t⟨r,⟩

instance [RenMap T (T::V)] : RenMap (Action T) (T::V) where
  rmap v := Action.rmap1 v

@[simp]
theorem Action.rmap1_re [RenMap T (T::V)] {r : RenVec (T::V)} {x : Nat}
  : (@re T x)⟨r,⟩ = re (r.head.act x)
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
theorem Action.rmap0_re [RenMap S V] [RenSuffix S V] {r : RenVec V} {x : Nat}
  : (@re S x)⟨r,⟩ = re x
:= by simp [RenMap.rmap]

@[simp]
theorem Action.rmap0_su [RenMap S V] [RenSuffix S V] {r : RenVec V} {t : S}
  : (su t)⟨r,⟩ = su t⟨r,⟩
:= by simp [RenMap.rmap]

@[simp]
def Action.smap1 [SubstMap T (T::V)] (σ : SubstVec (T::V)) : Action T -> Action T
| re x => σ.head.act x
| su t => su t[σ,]

instance [SubstMap T (T::V)] : SubstMap (Action T) (T::V) where
  smap v := Action.smap1 v

@[simp]
theorem Action.smap1_re [SubstMap T (T::V)] {σ : SubstVec (T::V)} {x : Nat}
  : (@re T x)[σ,] = σ.head.act x
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
theorem Action.smap0_re [SubstMap S V] [SubstSuffix S V] {σ : SubstVec V} {x : Nat}
  : (@re S x)[σ,] = re x
:= by simp [SubstMap.smap]

@[simp]
theorem Action.smap0_su [SubstMap S V] [SubstSuffix S V] {σ : SubstVec V} {t : S}
  : (su t)[σ,] = su t[σ,]
:= by simp [SubstMap.smap]

def Ren.id T : Ren T := ⟨λ x => x⟩
notation "r+0" => Ren.id _
notation "𝐫0(" T ")" => Ren.id T

@[reducible, simp]
def RenVec.id : (V : List (Type u2)) -> RenVec V
| [] => nil
| .cons x xs => .id x .: id xs

def Subst.id T : Subst T := ⟨λ x => re x⟩
notation "𝐬0" => Subst.id _
notation "𝐬0(" T ")" => Subst.id T

@[reducible, simp]
def SubstVec.id : (V : List (Type u2)) -> SubstVec V
| [] => nil
| .cons x xs => .id x .: id xs

def Ren.add T (k : Nat) : Ren T := ⟨(· + k)⟩

def Subst.add T (k : Nat) : Subst T := ⟨λ x => re $ x + k⟩

def Ren.sub T (k : Nat) : Ren T := ⟨(· - k)⟩

def Subst.sub T (k : Nat) : Subst T := ⟨λ x => re $ x - k⟩

def Ren.cons (a : Nat) (r : Ren T) : Ren T :=
  ⟨fun n => match n with
  | 0 => a
  | n + 1 => r.act n⟩

instance : AltCons Nat (Ren T) where
  altCons := Ren.cons

def Subst.cons (a : Action T) (σ : Subst T) : Subst T :=
  ⟨fun n => match n with
  | 0 => a
  | n + 1 => σ.act n⟩

instance : AltCons (Action T) (Subst T) where
  altCons := Subst.cons

def Ren.append : List Nat -> Ren T -> Ren T
| .nil, r => r
| .cons hd tl, r => hd .: append tl r

instance : HAppend (List Nat) (Ren T) (Ren T) where
  hAppend := Ren.append

instance : HAppend (Std.Rco Nat) (Ren T) (Ren T) where
  hAppend a := Ren.append a.toList

def Subst.append : List (Action T) -> Subst T -> Subst T
| .nil, r => r
| .cons hd tl, r => hd .: append tl r

instance : HAppend (List $ Action T) (Subst T) (Subst T) where
  hAppend := Subst.append

def Subst.append_ren : List Nat -> Subst T -> Subst T
| .nil, r => r
| .cons hd tl, r => re hd .: append_ren tl r

instance : HAppend (List Nat) (Subst T) (Subst T) where
  hAppend := Subst.append_ren

instance : HAppend (Std.Rco Nat) (Subst T) (Subst T) where
  hAppend a := Subst.append_ren a.toList

def Ren.compose : Ren T -> Ren T -> Ren T
| r1, r2 => .mk λ n => r2.act (r1.act n)

instance : AndThen (Ren T) where
  andThen r f := Ren.compose r (f ())

def RenVec.compose : {V : List (Type u2)} -> RenVec V -> RenVec V -> RenVec V
| _, nil, _ => nil
| .cons _ _, cons v1 v1s, cons v2 v2s => (v1 >> v2) .: compose v1s v2s

instance : AndThen (RenVec V) where
  andThen r f := RenVec.compose r (f ())

def Subst.compose_ren_left : Ren T -> Subst T -> Subst T
| r, τ => .mk λ n => τ.act (r.act n)

instance : HAndThen (Ren T) (Subst T) (Subst T) where
  hAndThen r f := Subst.compose_ren_left r (f ())

def SubstVec.compose_ren_left
  : {V : List (Type u2)} -> RenVec V -> SubstVec V -> SubstVec V
| [],  _, _ => .nil
| .cons _ _, .cons v1 v1s, cons v2 v2s => (v1 >> v2) .: compose_ren_left v1s v2s

instance : HAndThen (RenVec V) (SubstVec V) (SubstVec V) where
  hAndThen r f := SubstVec.compose_ren_left r (f ())

def Subst.compose_ren_right [RenMap T (T::V)] : Subst T -> RenVec (T::V) -> Subst T
| σ, r => .mk λ n => (σ.act n)⟨r,⟩

instance [RenMap T (T::V)] : HAndThen (Subst T) (RenVec (T::V)) (Subst T) where
  hAndThen σ f := Subst.compose_ren_right σ (f ())

def SubstVec.compose_ren_right
  : {V : List (Type u2)} -> [RenMapAll V] -> SubstVec V -> RenVec V -> SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, cons v1 v1s, v@(.cons _ v2s) => (v1 >> v) .: compose_ren_right v1s v2s

instance [RenMapAll V] : HAndThen (SubstVec V) (RenVec V) (SubstVec V) where
  hAndThen σ f := SubstVec.compose_ren_right σ (f ())

def Subst.compose [SubstMap T (T::V)] : Subst T -> SubstVec (T::V) -> Subst T
| σ, τ => .mk fun n => (σ.act n)[τ,]

instance [SubstMap T (T::V)] : HAndThen (Subst T) (SubstVec (T::V)) (Subst T) where
  hAndThen σ f := Subst.compose σ (f ())

def SubstVec.compose
  : {V : List (Type u2)} -> [SubstMapAll V] ->
    SubstVec V -> SubstVec V -> SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, cons v1 v1s, v@(cons _ v2s) => (v1 >> v) .: compose v1s v2s

instance [SubstMapAll V] : AndThen (SubstVec V) where
  andThen σ f := SubstVec.compose σ (f ())

def Ren.lift (r : Ren T) (k : Nat := 1) : Ren T := (0...k) ++ r >> add T k

@[simp]
def RenVec.lift : {V : List (Type u2)} -> RenVec V -> List Nat -> RenVec V
| [], _, _ => .nil
| _::_, cons t ts, [] => t .: ts
| _::_, cons t ts, k::ks => t.lift k .: ts.lift ks

def Subst.lift (V : List (Type u2)) [RenMap T (T::V)] (σ : Subst T) (k : Nat := 1) : Subst T :=
  (0...k) ++ σ >> (.add T k .: RenVec.id V)

@[simp]
def SubstVec.lift : {V : List (Type u2)} -> [RenMapAll V] -> List Nat -> SubstVec V ->  SubstVec V
| [], _, _, _ => .nil
| .cons _ _, _, [], cons t ts => t .: ts
| .cons _ Vs, _, .cons k ks, cons t ts => t.lift Vs k .: ts.lift ks

def Subst.act_list (σ : Subst T) : (ℓ : List Nat) -> List (Action T)
| [] => []
| .cons x xs => σ.act x :: act_list σ xs

instance : SubstAction T (List Nat) (List (Action T)) where
  act := Subst.act_list

def Ren.to (r : Ren T) : Subst T := ⟨λ x => re (r.act x)⟩

def RenVec.to : {V : List (Type u2)} -> RenVec V -> SubstVec V
| [], _ => .nil
| .cons _ _, cons r rs => r.to .: rs.to

class RenMapId (S : Type u1) (V : List (Type u2)) [RenMap S V] where
  id_law {s : S} : s⟨.id V,⟩ = s

@[simp]
theorem Ren.id_law [RenMap S V] [RenMapId S V] {s : S} : s⟨.id V,⟩ = s := RenMapId.id_law

class RenMapCompose (S : Type u1) (V : List (Type u2)) [RenMap S V] where
  compose_law {s : S} {r1 r2 : RenVec V} : s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩

@[simp]
theorem Ren.compose_law [RenMap S V] [RenMapCompose S V] {s : S} {r1 r2 : RenVec V}
  : s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
:= RenMapCompose.compose_law

class SubstMapStable (S : Type u1) (V : List $ Type u2) [RenMap S V] [SubstMap S V] where
  stable (r : RenVec V) (σ : SubstVec V) : r.to = σ -> rmap (S := S) r = smap σ

@[grind <-]
theorem Subst.stable
  [RenMap S V] [SubstMap S V] [SubstMapStable S V]
  {r : RenVec V} {σ : SubstVec V} (h : r.to = σ)
  : rmap (S := S) r = smap σ
:= SubstMapStable.stable _ _ h

class SubstMapId (S : Type u1) (V : List $ Type u2) [SubstMap S V] where
  id_law {s : S} : s[.id V,] = s

@[simp]
theorem Subst.id_law [SubstMap S V] [SubstMapId S V] {s : S} : s[.id V,] = s :=
  SubstMapId.id_law

class SubstMapRenComposeLeft (S : Type u1) (V : List $ Type u2) [RenMap S V] [SubstMap S V] where
  compose_left_law {s : S} {r : RenVec V} {τ : SubstVec V} : s⟨r,⟩[τ,] = s[r >> τ,]

@[simp]
theorem Subst.compose_left_law
  [RenMap S V] [SubstMap S V] [SubstMapRenComposeLeft S V]
  {s : S} {r : RenVec V} {τ : SubstVec V}
  : s⟨r,⟩[τ,] = s[r >> τ,]
:= SubstMapRenComposeLeft.compose_left_law

class SubstMapRenComposeRight (S : Type u1) (V : List $ Type u2)
  [RenMap S V] [RenMapAll V] [SubstMap S V]
where
  compose_right_law {s : S} {r : RenVec V} {σ : SubstVec V} : s[σ,]⟨r,⟩ = s[σ >> r,]

@[simp]
theorem Subst.compose_right_law
  [RenMap S V] [RenMapAll V] [SubstMap S V] [SubstMapRenComposeRight S V]
  {s : S} {σ : SubstVec V} {r : RenVec V}
  : s[σ,]⟨r,⟩ = s[σ >> r,]
:= SubstMapRenComposeRight.compose_right_law

class SubstMapCompose (S : Type u1) (V : List $ Type u2) [SubstMap S V] [SubstMapAll V] where
  compose_law {s : S} {σ τ : SubstVec V} : s[σ,][τ,] = s[σ >> τ,]

@[simp]
theorem Subst.compose_law
  [SubstMap S V] [SubstMapAll V] [SubstMapCompose S V]
  {s : S} {σ τ : SubstVec V}
  : s[σ,][τ,] = s[σ >> τ,]
:= SubstMapCompose.compose_law

end LeanSubst
