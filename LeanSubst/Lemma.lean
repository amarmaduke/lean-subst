module

public import LeanSubst.Basic
import all LeanSubst.Basic

namespace LeanSubst

universe u u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}
variable {V : List (Type u2)}

@[simp]
theorem Ren.id_action {x} : 𝐫0(T).act x = x := by simp [id]

@[simp]
theorem Subst.id_action {x} : 𝐬0(T).act x = re x := by simp [id, act, SubstAction.act]

@[simp]
theorem RenVec.id_head : (id $ T::V).head = .id T := by simp [id]

@[simp]
theorem SubstVec.id_head : (id $ T::V).head = .id T := by simp [id]

@[simp]
theorem SubstVec.id_tail : (id $ T::V).tail = id V := by simp [id]

@[simp]
theorem Ren.add_action {k x} : (add T k).act x = x + k := by simp [Ren.add]

@[simp]
theorem Subst.add_action {k x} : (add T k).act x = re (x + k) := by simp [add, act, SubstAction.act]

@[simp]
theorem Ren.add_zero : add T 0 = 𝐫0 := by simp [Ren.add, Ren.id]

@[simp]
theorem Subst.add_zero : add T 0 = 𝐬0 := by simp [add, id]

@[simp]
theorem Ren.sub_action {k x} : (sub T k).act x = x - k := by simp [sub]

@[simp]
theorem Subst.sub_action {k x} : (@sub T k).act x = re (x - k) := by
  simp [sub, act, SubstAction.act]

@[simp]
theorem Ren.sub_zero : sub T 0 = 𝐫0 := by simp [sub, id]

@[simp]
theorem Subst.sub_zero : sub T 0 = 𝐬0 := by simp [sub, id]

@[simp]
theorem Ren.cons_action0 {a} {r : Ren T} : (a.:r).act 0 = a := by
  simp [cons, AltCons.altCons]

@[simp]
theorem Subst.cons_action0 {a} {σ : Subst T} : (a.:σ).act 0 = a := by
  simp [AltCons.altCons, cons, act, SubstAction.act]

@[simp]
theorem Ren.cons_action {a i : Nat} {r : Ren T} : (a.:r).act (i + 1) = r.act i := by
  simp [cons, AltCons.altCons]

@[simp]
theorem Subst.cons_action {a i} {σ : Subst T} : (a.:σ).act (i + 1) = σ.act i := by
  simp [AltCons.altCons, cons, act, SubstAction.act]

@[simp]
theorem Ren.cons_add {T n} : n .: add T (n + 1) = add T n := by
  induction n <;> simp [id, AltCons.altCons, cons, *]
  case zero => grind
  case succ n ih =>
    simp [add] at *; grind

@[simp]
theorem Subst.cons_add {T n} : re n .: add T (n + 1) = add T n := by
  induction n <;> simp [id, AltCons.altCons, cons, *]
  case zero => grind
  case succ n ih =>
    simp [add] at *; grind

@[simp]
theorem Ren.append_nil {r : Ren T} : ([] : List Nat) ++ r = r := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Subst.append_nil {σ : Subst T} : ([] : List $ Action T) ++ σ = σ := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Subst.append_list_nil {σ : Subst T} : ([] : List $ Nat) ++ σ = σ := by
  simp [HAppend.hAppend, append_ren]

@[simp]
theorem Ren.append_cons {a} {ℓ : List Nat} {r : Ren T} : (a::ℓ) ++ r = a.:(ℓ ++ r) := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Subst.append_cons {a} {ℓ : List $ Action T} {σ : Subst T} : (a::ℓ) ++ σ = a.:(ℓ ++ σ) := by
  simp [HAppend.hAppend, append]

@[simp]
theorem Subst.append_list_cons {a} {ℓ : List Nat} {σ : Subst T} : (a::ℓ) ++ σ = re a.:(ℓ ++ σ) := by
  simp [HAppend.hAppend, append_ren]

@[simp, grind <-]
theorem Ren.append_action_lt {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_action_lt {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_action_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_list_action_lt {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = re ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_list_action_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Ren.append_action_ge {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge r i tl (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.append_action_ge {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_action_ge σ i tl (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.append_list_action_ge {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_list_action_ge σ i tl (by grind) |> cast (by simp)

@[simp]
theorem Ren.cons_add_is_id {k} : k .: add _ (k + 1) = id T := sorry

@[simp]
theorem Subst.cons_add_is_id {k} : re k .: add _ (k + 1) = id T := sorry

@[simp]
theorem Ren.append_range_add_is_add_min : ∀ {s e}, (s...e) ++ add T e = add T (min s e) := sorry

@[simp]
theorem Subst.append_range_add_is_add_min : ∀ {s e}, (s...e) ++ add T e = add T (min s e) := sorry

@[simp]
theorem Ren.compose_action {r1 r2 : Ren T} {x} : (r1 >> r2).act x = r2.act (r1.act x) := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_left_action {r : Ren T} {τ : Subst T} {x : Nat}
  : (r >> τ).act x = τ.act (r.act x)
:= by simp [HAndThen.hAndThen, compose_left, act, SubstAction.act]

@[simp]
theorem Subst.compose_right_action [RenMap T (T::V)] {σ : Subst T} {r : RenVec $ T::V} {x : Nat}
  : (σ >> r).act x = (σ.act x)⟨r,⟩
:= by simp [HAndThen.hAndThen, compose_right, act, SubstAction.act]

@[simp]
theorem Subst.compose_action [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec $ T::V} {x : Nat}
  : (σ >> τ).act x = (σ.act x)[τ,]
:= by simp [HAndThen.hAndThen, compose, act, SubstAction.act]

@[simp]
theorem RenVec.compose_head {σ τ : RenVec (T::V)} : (σ >> τ).head = σ.head >> τ.head := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_left_head {r : RenVec (T::V)} {τ : SubstVec (T::V)}
  : (r >> τ).head = r.head >> τ.head
:= by
  rcases r with ⟨r, r'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem SubstVec.compose_right_head [RenMapAll (T::V)] {σ : SubstVec (T::V)} {r : RenVec (T::V)}
  : (σ >> r).head = σ.head >> r
:= by
  rcases σ with ⟨σ, σ'⟩
  rcases r with ⟨r, r'⟩
  simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_head [SubstMapAll (T::V)] {σ τ : SubstVec (T::V)}
  : (σ >> τ).head = σ.head >> τ
:= by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_tail {σ τ : RenVec (T::V)} : (σ >> τ).tail = σ.tail >> τ.tail := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_left_tail {r : RenVec (T::V)} {τ : SubstVec (T::V)}
  : (r >> τ).tail = r.tail >> τ.tail
:= by
  rcases r with ⟨r, r'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem SubstVec.compose_right_tail [RenMapAll (T::V)] {σ : SubstVec (T::V)} {r : RenVec (T::V)}
  : (σ >> r).tail = σ.tail >> r.tail
:= by
  rcases σ with ⟨σ, σ'⟩
  rcases r with ⟨r, r'⟩
  simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_tail [SubstMapAll (T::V)] {σ τ : SubstVec (T::V)}
  : (σ >> τ).tail = σ.tail >> τ.tail
:= by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

public instance [RenMap T (T::V)] [RenMapId T (T::V)] : RenMapId (Action T) (T::V) where
  id_law := by intro s; cases s <;> simp

public instance [RenMap S V] [RenSuffix S V] [RenMapId S V] : RenMapId (Action S) V where
  id_law := by intro s; cases s <;> simp

public instance [RenMap T (T::V)] [RenMapCompose T (T::V)] : RenMapCompose (Action T) (T::V) where
  compose_law := by intro s r1 r2; cases s <;> simp

public instance [RenMap S V] [RenSuffix S V] [RenMapCompose S V] : RenMapCompose (Action S) V where
  compose_law := by intro s; cases s <;> simp

public instance [SubstMap T (T::V)] [SubstMapId T (T::V)] : SubstMapId (Action T) (T::V) where
  id_law := by intro s; cases s <;> simp

public instance [SubstMap S V] [SubstSuffix S V] [SubstMapId S V] : SubstMapId (Action S) V where
  id_law := by intro s; cases s <;> simp

public instance
  [RenMap T (T::V)] [SubstMap T (T::V)] [SubstMapRenComposeLeft T (T::V)]
  : SubstMapRenComposeLeft (Action T) (T::V)
where
  compose_left_law := by intro s r τ; cases s <;> simp

public instance
  [RenMap S V] [RenSuffix S V] [SubstMap S V] [SubstSuffix S V] [SubstMapRenComposeLeft S V]
  : SubstMapRenComposeLeft (Action S) V
where
  compose_left_law := by intro s; cases s <;> simp

public instance
  [RenMapAll (T::V)] [SubstMap T (T::V)] [SubstMapRenComposeRight T (T::V)]
  : SubstMapRenComposeRight (Action T) (T::V)
where
  compose_right_law := by intro s r τ; cases s <;> simp

public instance
  [RenMap S V] [RenMapAll V] [RenSuffix S V]
  [SubstMap S V] [SubstSuffix S V] [SubstMapRenComposeRight S V]
  : SubstMapRenComposeRight (Action S) V
where
  compose_right_law := by intro s; cases s <;> simp

public instance [SubstMapAll (T::V)] [SubstMapCompose T (T::V)] : SubstMapCompose (Action T) (T::V)
where
  compose_law := by intro s r τ; cases s <;> simp

public instance [SubstMap S V] [SubstMapAll V] [SubstSuffix S V] [SubstMapCompose S V]
  : SubstMapCompose (Action S) V
where
  compose_law := by intro s; cases s <;> simp

@[simp]
theorem Ren.compose_sub_add {k} : add T k >> sub T k = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, id, compose]

@[simp]
theorem Subst.compose_left_sub_add {k} : Ren.add T k >> sub T k = id T := by
  simp [HAndThen.hAndThen, sub, id, compose_left]

@[simp]
theorem Subst.compose_right_sub_add [RenMap T (T::V)] {r : RenVec V} {k}
  : add T k >> (.sub T k .: r) = id T
:= by simp [HAndThen.hAndThen, add, id, compose_right]

@[simp]
theorem Subst.compose_sub_add [SubstMap T (T::V)] {σ : SubstVec V} {k}
  : add T k >> (sub T k .: σ) = id T
:= by simp [HAndThen.hAndThen, sub, add, id, compose]

@[simp]
theorem Ren.compose_add_add {n m} : add T n >> add T m = add T (n + m) := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose]; grind

@[simp]
theorem Subst.compose_left_add_add {n m} : Ren.add T n >> add T m = add T (n + m) := by
  simp [HAndThen.hAndThen, add, compose_left]; grind

@[simp]
theorem Subst.compose_right_add_add [RenMap T (T::V)] {r : RenVec V} {n m}
  : add T n >> (.add T m .: r) = add T (n + m)
:= by simp [HAndThen.hAndThen, add, compose_right]; grind

@[simp]
theorem Subst.compose_add_add [SubstMap T (T::V)] {σ : SubstVec V} {n m}
  : add T n >> (add T m .: σ) = add T (n + m)
:= by simp [HAndThen.hAndThen, add, compose]; grind

@[simp]
theorem Ren.compose_sub_sub {n m} : sub T n >> sub T m = sub T (n + m) := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, compose]; grind

@[simp]
theorem Subst.compose_left_sub_sub {n m} : Ren.sub T n >> sub T m = sub T (n + m) := by
  simp [HAndThen.hAndThen, sub, compose_left]; grind

@[simp]
theorem Subst.compose_right_sub_sub [RenMap T (T::V)] {r : RenVec V} {n m}
  : sub T n >> (.sub T m .: r) = sub T (n + m)
:= by simp [HAndThen.hAndThen, sub, compose_right]; grind

@[simp]
theorem Subst.compose_sub_sub [SubstMap T (T::V)] {σ : SubstVec V} {n m}
  : sub T n >> (sub T m .: σ) = sub T (n + m)
:= by simp [HAndThen.hAndThen, sub, compose]; grind

@[simp]
theorem RenVec.compose_empty : ∀ {r1 r2 : RenVec []}, r1 >> r2 = ·⟨⟩
| nil, nil => by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem SubstVec.compose_left_empty : ∀ {r : RenVec []} {τ : SubstVec []}, r >> τ = ·[]
| .nil, nil => by simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem SubstVec.compose_right_empty [RenMapAll []]
  : ∀ {σ : SubstVec []} {r : RenVec []}, σ >> r = ·[]
| nil, .nil => by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_empty [SubstMapAll []] : ∀ {σ τ : SubstVec []}, σ >> τ = ·[]
| nil, nil => by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_cons {r1 r2 : Ren T} {k} : (k .: r1) >> r2 = r2.act k .: (r1 >> r2) := by
  simp [HAndThen.hAndThen, AndThen.andThen, AltCons.altCons, cons, compose]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem RenVec.compose_cons {r1 : Ren T} {r1s : RenVec V} : ∀ {r2s : RenVec (T::V)},
  (r1 .: r1s) >> r2s = (r1 >> r2s.head) .: (r1s >> r2s.tail)
| cons r2 r2s => by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_left_cons {r : Ren T} {τ : Subst T} {k}
  : (k .: r) >> τ = τ.act k .: (r >> τ)
:= by
  simp [HAndThen.hAndThen, AltCons.altCons, Ren.cons, cons, compose_left]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.compose_right_cons [RenMap T (T::V)] {σ : Subst T} {r : RenVec (T::V)} {a}
  : (a .: σ) >> r = a⟨r,⟩ .: (σ >> r)
:= by
  simp [HAndThen.hAndThen, AltCons.altCons, cons, compose_right]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.compose_cons [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)} {a}
  : (a .: σ) >> τ = a[τ,] .: (σ >> τ)
:= by
  simp [HAndThen.hAndThen, AltCons.altCons, cons, compose]
  funext; case _ x =>
  cases x <;> simp

@[simp]
theorem SubstVec.compose_left_cons {r1 : Ren T} {r1s : RenVec V} : ∀ {σ2s : SubstVec (T::V)},
  (r1 .: r1s) >> σ2s = (r1 >> σ2s.head) .: (r1s >> σ2s.tail)
| cons σ2 σ2s => by simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem SubstVec.compose_right_cons
  [RenMapAll (T::V)] {σ1 : Subst T} {σ1s : SubstVec V} : ∀ {r2s : RenVec (T::V)},
  (σ1 .: σ1s) >> r2s = (σ1 >> r2s) .: (σ1s >> r2s.tail)
| .cons r2 r2s => by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_cons
  [SubstMapAll (T::V)] {σ1 : Subst T} {σ1s : SubstVec V} : ∀ {σ2s : SubstVec (T::V)},
  (σ1 .: σ1s) >> σ2s = (σ1 >> σ2s) .: (σ1s >> σ2s.tail)
| cons r2 r2s => by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_id_left {r : Ren T} : 𝐫0 >> r = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem RenVec.compose_id_left : ∀ {V : List (Type u2)} {r : RenVec V}, id V >> r = r
| [], nil => by simp [id]
| V::Vs, cons r rs => by simp [id, compose_id_left]

@[simp]
theorem Subst.compose_left_id_left {σ : Subst T} : 𝐫0(T) >> σ = σ := by
  simp [HAndThen.hAndThen, compose_left]; congr

@[simp]
theorem Subst.compose_right_id_left [RenMap T (T::V)] {r : RenVec (T::V)}
  : 𝐬0(T) >> r = r.head.to
:= by simp [HAndThen.hAndThen, compose_right]; congr

@[simp]
theorem Subst.compose_id_left [SubstMap T (T::V)] {σ : SubstVec (T::V)}
  : 𝐬0(T) >> σ = σ.head
:= by simp [HAndThen.hAndThen, compose]; congr

@[simp]
theorem SubstVec.compose_left_id_left : ∀ {V} {σ : SubstVec V}, RenVec.id V >> σ = σ
| [], nil => by simp
| _::Vs, cons σ σs =>
  have ih := compose_left_id_left (V := Vs) (σ := σs)
  by simp [RenVec.id, ih]

@[simp]
theorem SubstVec.compose_right_id_left  : ∀ {V} [RenMapAll V] {r : RenVec V}, id V >> r = r.to
| [], _, .nil => by simp [RenVec.to]
| _::Vs, _, .cons r rs =>
  have ih := compose_right_id_left (V := Vs) (r := rs)
  by simp [id, ih, RenVec.to]

@[simp]
theorem SubstVec.compose_id_left  : ∀ {V} [SubstMapAll V] {σ : SubstVec V}, id V >> σ = σ
| [], _, nil => by simp
| _::Vs, _, cons σ σs =>
  have ih := compose_id_left (V := Vs) (σ := σs)
  by simp [id, ih]

@[simp]
theorem Ren.compose_id_right {r : Ren T} : r >> 𝐫0 = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem RenVec.compose_id_right : ∀ {V} {r : RenVec V}, r >> id V = r
| [], nil => by simp
| _::_, cons r rs => by simp [id, compose_id_right]

@[simp]
theorem Subst.compose_left_id_right {r : Ren T} : r >> 𝐬0(T) = r.to := by
  simp [HAndThen.hAndThen, compose_left]; congr

@[simp]
theorem Subst.compose_right_id_right [RenMap T (T::V)] [RenMapId T (T::V)] {σ : Subst T}
  : σ >> RenVec.id (T::V) = σ
:= by simp [HAndThen.hAndThen, compose_right]; congr

@[simp]
theorem Subst.compose_id_right [SubstMap T (T::V)] [SubstMapId T (T::V)] {σ : Subst T}
  : σ >> SubstVec.id (T::V) = σ
:= by simp [HAndThen.hAndThen, compose]; congr

-- @[simp]
-- theorem SubstVec.compose_id_right : ∀ {V} [SubstMapAll V] {σ : SubstVec V}, σ >> id V = σ
-- | [], _, nil => by simp
-- | _::_, _, cons σ σs => by simp; sorry

@[simp]
theorem Ren.compose_assoc {r1 r2 r3 : Ren T} : (r1 >> r2) >> r3 = r1 >> r2 >> r3 := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_assoc_rrs
  {r1 : Ren T} {r2 : Ren T} {s3 : Subst T}
  : (r1 >> r2) >> s3 = r1 >> r2 >> s3
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose_left, Ren.compose]

@[simp]
theorem Subst.compose_assoc_rsr [RenMapAll (T::V)]
  {r1 : Ren T} {s2 : Subst T} {r3 : RenVec (T::V)}
  : (r1 >> s2) >> r3 = r1 >> s2 >> r3
:= by simp [HAndThen.hAndThen, compose_left, compose_right]

@[simp]
theorem Subst.compose_assoc_rss [SubstMapAll (T::V)]
  {r1 : Ren T} {s2 : Subst T} {s3 : SubstVec (T::V)}
  : (r1 >> s2) >> s3 = r1 >> s2 >> s3
:= by simp [HAndThen.hAndThen, compose_left, compose]

@[simp]
theorem Subst.compose_assoc_srr [RenMapAll (T::V)] [RenMapCompose T (T::V)]
  {s1 : Subst T} {r2 : RenVec (T::V)} {r3 : RenVec (T::V)}
  : (s1 >> r2) >> r3 = s1 >> r2 >> r3
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose_right]

@[simp]
theorem Subst.compose_assoc_srs
  [RenMapAll (T::V)] [SubstMapAll (T::V)] [SubstMapRenComposeLeft T (T::V)]
  {s1 : Subst T} {r2 : RenVec (T::V)} {s3 : SubstVec (T::V)}
  : (s1 >> r2) >> s3 = s1 >> r2 >> s3
:= by simp [HAndThen.hAndThen, compose_right, compose]

@[simp]
theorem Subst.compose_assoc_ssr
  [RenMapAll (T::V)] [SubstMapAll (T::V)] [SubstMapRenComposeRight T (T::V)]
  {s1 : Subst T} {s2 : SubstVec (T::V)} {r3 : RenVec (T::V)}
  : (s1 >> s2) >> r3 = s1 >> s2 >> r3
:= by simp [HAndThen.hAndThen, compose_right, compose]

@[simp]
theorem Subst.compose_assoc [SubstMapAll (T::V)] [SubstMapCompose T (T::V)]
  {s1 : Subst T} {s2 : SubstVec (T::V)} {s3 : SubstVec (T::V)}
  : (s1 >> s2) >> s3 = s1 >> s2 >> s3
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.lift_compose {r1 r2 : Ren T} {k} : (r1 >> r2).lift k = r1.lift k >> r2.lift k := sorry

@[simp]
theorem RenVec.lift_compose {r1 r2 : RenVec V} {k} : (r1 >> r2).lift k = r1.lift k >> r2.lift k := sorry

@[simp]
theorem Subst.lift_compose_left [RenMap T (T::V)] {r : Ren T} {τ : Subst T} {k : Nat}
  : (r >> τ).lift V k = r.lift k >> τ.lift V k
:= sorry

@[simp]
theorem SubstVec.lift_compose_left [RenMapAll V] {r : RenVec V} {τ : SubstVec V} {k}
  : (r >> τ).lift k = r.lift k >> τ.lift k
:= sorry

@[simp]
theorem Subst.lift_compose_right [RenMap T (T::V)] {σ : Subst T} {r : RenVec (T::V)} {k : Nat}
  : (σ >> r).lift V k = σ.lift V k >> r.lift [k]
:= sorry

@[simp]
theorem SubstVec.lift_compose_right [RenMapAll V] {σ : SubstVec V} {r : RenVec V} {k}
  : (σ >> r).lift k = σ.lift k >> r.lift k
:= sorry

theorem Subst.lift_compose1
  [RenMapAll (T::V)] [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)}
  : (σ >> τ).lift V = σ.lift V >> τ.lift [1]
:= by
  cases τ; case _ τ τs =>
  simp [lift, SubstVec.lift]
  sorry

@[simp]
theorem Subst.lift_compose
  [RenMapAll (T::V)] [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)}
  : ∀ {k}, (σ >> τ).lift V k = σ.lift V k >> τ.lift [k]
| 0 => by sorry
| k + 1 => sorry

-- @[simp]
-- theorem SubstVec.lift_compose
--   : ∀ {V : List (Type u2)} [RenMapAll V] [SubstMapAll V] {σ τ : SubstVec V} {k},
--     (σ >> τ).lift k = σ.lift k >> τ.lift k
-- | [], _, _, _, _, _ => by simp [lift]
-- | V::Vs, _, _, .cons σ σs, .cons τ τs, [] => by simp [lift]
-- | V::Vs, _, _, .cons σ σs, .cons τ τs, k::ks => by simp [lift, lift_compose]; sorry

end LeanSubst
