module

public import LeanSubst.Basic
import all LeanSubst.Basic

namespace LeanSubst

public section

universe u u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}
variable {V : List (Type u2)}

@[ext]
theorem Ren.ext {r1 r2 : Ren T} : (∀ x, r1.act x = r2.act x) -> r1 = r2 := by
  intro h; rcases r1 with ⟨r1⟩; rcases r2 with ⟨r2⟩; simp at *
  ext; apply h

@[ext]
theorem Subst.ext {σ τ : Subst T} : (∀ x, σ.act x = τ.act x) -> σ = τ := by
  intro h; rcases σ with ⟨σ⟩; rcases τ with ⟨τ⟩; simp at *
  ext; apply h

@[simp]
theorem Ren.actl_nil {r : Ren T} : r.actl [] = [] := by simp [actl]

@[simp]
theorem Subst.actl_nil {σ : Subst T} : σ.actl [] = [] := by simp [actl]

@[simp]
theorem Ren.actl_cons {r : Ren T} {x xs} : r.actl (x::xs) = r.act x :: r.actl xs := by simp [actl]

@[simp]
theorem Subst.actl_cons {σ : Subst T} {x xs} : σ.actl (x::xs) = σ.act x :: σ.actl xs := by
  simp [actl]

@[simp]
theorem Ren.append_list_to_range {r : Ren T} {s e : Nat}
  : List.range' s (e - s) ++ r = (s...e) ++ r
:= by simp [HAppend.hAppend]

@[simp]
theorem Subst.append_list_to_range {σ : Subst T} {s e : Nat}
  : List.range' s (e - s) ++ σ = (s...e) ++ σ
:= by simp [HAppend.hAppend]

@[simp]
theorem Subst.append_list_to_range_map_re {σ : Subst T} {s e : Nat}
  : (List.map (@re T) $ List.range' s (e - s)) ++ σ = (s...e) ++ σ
:= by
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e; simp [append, append_ren]; case _ n ih =>
  have lem : e - (s + 1) = n := by grind
  simp [List.range'_succ, append, append_ren, ih lem]

@[simp, grind =]
theorem Ren.actr_ge {r : Ren T} {s e} (h : s ≥ e) : r.actr s e = [] := by
  have lem : e - s = 0 := by grind
  simp [actr, lem]

@[simp, grind =]
theorem Subst.actr_ge {σ : Subst T} {s e} (h : s ≥ e) : σ.actr s e = [] := by
  have lem : e - s = 0 := by grind
  simp [actr, lem]

@[grind =]
theorem Ren.actr_lt {r : Ren T} {s e} (h : s < e) : r.actr s e = r.act s :: r.actr (s + 1) e := by
  simp [actr]
  generalize ndef : e - s = n
  induction n generalizing s e
  case zero =>
    have lem : e = 0 := by grind
    subst lem; cases h
  case succ n ih =>
    simp [List.range'_succ]
    congr; grind

@[grind =]
theorem Subst.actr_lt {σ : Subst T} {s e} (h : s < e)
  : σ.actr s e = σ.act s :: σ.actr (s + 1) e
:= by
  simp [actr]
  generalize ndef : e - s = n
  induction n generalizing s e
  case zero =>
    have lem : e = 0 := by grind
    subst lem; cases h
  case succ n ih =>
    simp [List.range'_succ]
    congr; grind

@[simp]
theorem Ren.actl_is_actr {r : Ren T} {s e} : r.actl (List.range' s (e - s)) = r.actr s e := by
  simp [actr, actl]

@[simp]
theorem Subst.actl_is_actr {σ : Subst T} {s e} : σ.actl (List.range' s (e - s)) = σ.actr s e := by
  simp [actr, actl]

@[simp]
theorem Ren.id_act {x} : 𝐫0(T).act x = x := by simp [id]

@[simp]
theorem Subst.id_act {x} : 𝐬0(T).act x = re x := by simp [id]

@[simp]
theorem Ren.id_actr {s e : Nat} : 𝐫0(T).actr s e = List.range' s (e - s) := by
  simp [actr]
  generalize ndef : e - s = n
  induction n generalizing e s <;> simp [List.range'_succ]; case _ n ih =>
  have lem : e - (s + 1) = n := by grind
  rw [ih lem]

@[simp]
theorem Subst.id_actr {s e : Nat} : 𝐬0(T).actr s e = List.map re (List.range' s (e - s)) := by
  simp [actr]

@[simp]
theorem RenVec.id_head : (id $ T::V).head = .id T := by simp [id]

@[simp]
theorem SubstVec.id_head : (id $ T::V).head = .id T := by simp [id]

@[simp]
theorem SubstVec.id_tail : (id $ T::V).tail = id V := by simp [id]

@[simp]
theorem Ren.add_act {k x} : (add T k).act x = x + k := by simp [Ren.add]

@[simp]
theorem Subst.add_act {k x} : (add T k).act x = re (x + k) := by simp [add]

@[simp]
theorem Ren.add_zero : add T 0 = 𝐫0 := by simp [Ren.add, Ren.id]

@[simp]
theorem Subst.add_zero : add T 0 = 𝐬0 := by simp [add, id]

@[simp]
theorem Ren.sub_act {k x} : (sub T k).act x = x - k := by simp [sub]

@[simp]
theorem Subst.sub_act {k x} : (@sub T k).act x = re (x - k) := by
  simp [sub]

@[simp]
theorem Ren.sub_zero : sub T 0 = 𝐫0 := by simp [sub, id]

@[simp]
theorem Subst.sub_zero : sub T 0 = 𝐬0 := by simp [sub, id]

@[simp]
theorem Ren.cons_act0 {a} {r : Ren T} : (a.:r).act 0 = a := by
  simp [cons, AltCons.altCons]

@[simp]
theorem Subst.cons_act0 {a} {σ : Subst T} : (a.:σ).act 0 = a := by
  simp [AltCons.altCons, cons]

@[simp]
theorem Ren.cons_act {a i : Nat} {r : Ren T} : (a.:r).act (i + 1) = r.act i := by
  simp [cons, AltCons.altCons]

@[simp]
theorem Subst.cons_act {a i} {σ : Subst T} : (a.:σ).act (i + 1) = σ.act i := by
  simp [AltCons.altCons, cons]

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
theorem RenVec.head_id : (id (T::V)).head = Ren.id T := by simp [id]

@[simp]
theorem SubstVec.head_id : (id (T::V)).head = Subst.id T := by simp [id]

@[simp]
theorem RenVec.tail_id : (id (T::V)).tail = id V := by simp [id]

@[simp]
theorem SubstVec.tail_id : (id (T::V)).tail = id V := by simp [id]

@[simp]
theorem RenVec.cons_id : (Ren.id T .: id V) = id (T::V) := by simp [id]

@[simp]
theorem SubstVec.cons_id : (Subst.id T .: id V) = id (T::V) := by simp [id]

@[simp]
theorem RenVec.cons_id_nil : (Ren.id T .: nil) = id [T] := by simp [id]

@[simp]
theorem SubstVec.cons_id_nil : (Subst.id T .: nil) = id [T] := by simp [id]

@[simp]
theorem RenVec.cons_head_id_nil {r : Ren T} : r .: id [] = r .: nil := by simp [id]

@[simp]
theorem SubstVec.cons_head_id_nil {σ : Subst T} : σ .: id [] = σ .: nil := by simp [id]

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

@[simp]
theorem Ren.append_empty_range {r : Ren T} {s e : Nat} {h : e ≤ s} : (s...e) ++ r = r := by
  simp [HAppend.hAppend]
  have lem : e - s = 0 := by grind
  rw [lem]; simp [append]

@[simp]
theorem Subst.append_empty_range {σ : Subst T} {s e : Nat} {h : e ≤ s} : (s...e) ++ σ = σ := by
  simp [HAppend.hAppend]
  have lem : e - s = 0 := by grind
  rw [lem]; simp [append_ren]

@[simp, grind <-]
theorem Ren.append_act_lt {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_act_lt (r := r) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Ren.append_range_act_lt {r : Ren T} {i} {s e : Nat} (h : i < e - s)
  : ((s...e) ++ r).act i = s + i
:= by
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e i; rw [ndef] at h; cases h; case _ n ih =>
  simp [List.range'_succ, append]
  cases i <;> simp; case _ i =>
  have lem1 : e - (s + 1) = n := by grind
  have lem2 : i < e - (s + 1) := by grind
  rw [ih lem2 lem1]; grind

@[simp, grind <-]
theorem Subst.append_act_lt {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_act_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_list_act_lt {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = re ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => append_list_act_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.append_range_act_lt {σ : Subst T} {i} {s e : Nat} (h : i < e - s)
  : ((s...e) ++ σ).act i = re (s + i)
:= by
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e i; rw [ndef] at h; cases h; case _ n ih =>
  simp [List.range'_succ, append_ren]
  cases i <;> simp; case _ i =>
  have lem1 : e - (s + 1) = n := by grind
  have lem2 : i < e - (s + 1) := by grind
  rw [ih lem2 lem1]; grind

@[simp, grind <-]
theorem Ren.append_act_ge {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_act_ge r i tl (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Ren.append_range_act_ge {r : Ren T} {i} {s e : Nat} (h : i ≥ e - s)
  : ((s...e) ++ r).act i = r.act (i - (e - s))
:= by
  have lem : i ≥ List.length (List.range' s (e - s)) := by simp [h]
  have lem2 := Ren.append_act_ge (r := r) lem
  simp [HAppend.hAppend] at lem2
  simp [HAppend.hAppend, lem2]

@[simp, grind <-]
theorem Subst.append_act_ge {σ : Subst T} {i}
  : {ℓ : List $ Action T} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_act_ge σ i tl (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.append_list_act_ge {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => @append_list_act_ge σ i tl (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.append_range_act_ge {σ : Subst T} {i} {s e : Nat} (h : i ≥ e - s)
  : ((s...e) ++ σ).act i = σ.act (i - (e - s))
:= by
  have lem : i ≥ List.length (List.range' s (e - s)) := by simp [h]
  have lem2 := Subst.append_list_act_ge (σ := σ) lem
  simp [HAppend.hAppend] at lem2
  simp [HAppend.hAppend, lem2]

@[simp]
theorem Ren.append_range_add : ∀ {s e}, (s...e) ++ add T e = add T (min s e) := by
  intro s e
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e; simp [append]; grind; case _ n ih =>
  have lem : e - (s + 1) = n := by grind
  have lem2 : s < e := by grind
  simp [List.range'_succ, append, ih lem]
  ext; case _ i =>
  cases i <;> simp <;> grind

@[simp]
theorem Subst.append_range_add : ∀ {s e}, (s...e) ++ add T e = add T (min s e) := by
  intro s e
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e; simp [append_ren]; grind; case _ n ih =>
  have lem : e - (s + 1) = n := by grind
  have lem2 : s < e := by grind
  simp [List.range'_succ, append_ren, ih lem]
  ext; case _ i =>
  cases i <;> simp <;> grind

@[simp]
theorem Ren.append_range_to_cons {r : Ren T} {s e} (h : s < e)
  : (s...e) ++ r = s .: (((s+1)...e) ++ r)
:= by
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e r; lia; case _ n ih =>
  have lem : e - (s + 1) = n := by lia
  simp [List.range'_succ, append, *]

@[simp]
theorem Subst.append_range_to_cons {σ : Subst T} {s e} (h : s < e)
  : (s...e) ++ σ = re s .: (((s+1)...e) ++ σ)
:= by
  simp [HAppend.hAppend]
  generalize ndef : e - s = n
  induction n generalizing s e σ; lia; case _ n ih =>
  have lem : e - (s + 1) = n := by lia
  simp [List.range'_succ, append_ren, *]

@[simp]
theorem Ren.compose_act {r1 r2 : Ren T} {x} : (r1 >> r2).act x = r2.act (r1.act x) := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_left_act {r : Ren T} {τ : Subst T} {x : Nat}
  : (r >> τ).act x = τ.act (r.act x)
:= by simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem Subst.compose_right_act [RenMap T (T::V)] {σ : Subst T} {r : RenVec $ T::V} {x : Nat}
  : (σ >> r).act x = (σ.act x)⟨r,⟩
:= by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem Subst.compose_act [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec $ T::V} {x : Nat}
  : (σ >> τ).act x = (σ.act x)[τ,]
:= by simp [HAndThen.hAndThen, compose]

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
theorem SubstVec.compose_right_head :
  ∀ [RenMapAll (T::V)] {σ : SubstVec (T::V)} {r : RenVec (T::V)}, (σ >> r).head = σ.head >> r
| RenMapAll.cons _, cons σ σs, .cons r rs => by simp [HAndThen.hAndThen, compose_right]

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
theorem SubstVec.compose_right_tail [RenMapAll (T::V)] :
  ∀ {σ : SubstVec (T::V)} {r : RenVec (T::V)}, (σ >> r).tail = σ.tail >> r.tail
| .cons _ _, .cons _ _ => by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_tail [SubstMapAll (T::V)] {σ τ : SubstVec (T::V)}
  : (σ >> τ).tail = σ.tail >> τ.tail
:= by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

instance [RenMap T (T::V)] [RenMapId T (T::V)] : RenMapId (Action T) (T::V) where
  id_law := by intro s; cases s <;> simp

instance [RenMap S V] [RenSuffix S V] [RenMapId S V] : RenMapId (Action S) V where
  id_law := by intro s; cases s <;> simp

instance [RenMap T (T::V)] [RenMapComp T (T::V)] : RenMapComp (Action T) (T::V) where
  compose_law := by intro s r1 r2; cases s <;> simp

instance [RenMap S V] [RenSuffix S V] [RenMapComp S V] : RenMapComp (Action S) V where
  compose_law := by intro s; cases s <;> simp

instance [SubstMap T (T::V)] [SubstMapId T (T::V)] : SubstMapId (Action T) (T::V) where
  id_law := by intro s; cases s <;> simp

instance [SubstMap S V] [SubstSuffix S V] [SubstMapId S V] : SubstMapId (Action S) V where
  id_law := by intro s; cases s <;> simp

instance
  [RenMap T (T::V)] [SubstMap T (T::V)] [SubstMapRenCompLeft T (T::V)]
  : SubstMapRenCompLeft (Action T) (T::V)
where
  compose_left_law := by intro s r τ; cases s <;> simp

instance
  [RenMap S V] [RenSuffix S V] [SubstMap S V] [SubstSuffix S V] [SubstMapRenCompLeft S V]
  : SubstMapRenCompLeft (Action S) V
where
  compose_left_law := by intro s; cases s <;> simp

instance
  [RenMapAll (T::V)] [SubstMap T (T::V)] [SubstMapRenCompRight T (T::V)]
  : SubstMapRenCompRight (Action T) (T::V)
where
  compose_right_law := by intro s r τ; cases s <;> simp

instance
  [RenMap S V] [RenMapAll V] [RenSuffix S V]
  [SubstMap S V] [SubstSuffix S V] [SubstMapRenCompRight S V]
  : SubstMapRenCompRight (Action S) V
where
  compose_right_law := by intro s; cases s <;> simp

instance [SubstMapAll (T::V)] [SubstMapComp T (T::V)] : SubstMapComp (Action T) (T::V)
where
  compose_law := by intro s r τ; cases s <;> simp

instance [SubstMap S V] [SubstMapAll V] [SubstSuffix S V] [SubstMapComp S V]
  : SubstMapComp (Action S) V
where
  compose_law := by intro s; cases s <;> simp

instance [RenMap T (T::V)] [SubstMap T (T::V)] [SubstMapStable T (T::V)]
  : SubstMapStable (Action T) (T::V)
where
  stable := by
    intro r σ h; subst h
    cases r; case _ r rs =>
    funext; case _ a =>
    cases a <;> simp [RenVec.to, Ren.to]
    rw [Subst.stable (σ := r.to .: rs.to)]; congr
    simp [RenVec.to]

def List.rmap [RenMap S V] (r : RenVec V) : List S -> List S
| [] => []
| x::xs => x⟨r,⟩ :: rmap r xs

instance [RenMap S V] : RenMap (List S) V where
  rmap := List.rmap

@[simp]
theorem List.rmap_fix [RenMap S V] {r : RenVec V} {l : List S} : rmap r l = l⟨r,⟩ := by
  simp only [RenMap.rmap]

@[simp]
theorem List.rmap_nil [RenMap S V] {r : RenVec V} : ([] : List S)⟨r,⟩ = [] := by
  simp only [RenMap.rmap, rmap]

@[simp]
theorem List.rmap_cons [RenMap S V] {r : RenVec V} {x} {xs : List S}
  : (x::xs)⟨r,⟩ = x⟨r,⟩::xs⟨r,⟩
:= by simp only [RenMap.rmap, rmap]

instance [RenMap S V] [RenMapId S V] : RenMapId (List S) V where
  id_law := by intro s; induction s <;> simp [*]

instance [RenMap S V] [RenMapComp S V] : RenMapComp (List S) V where
  compose_law := by intro s; induction s <;> simp [*]

def List.smap [SubstMap S V] (σ : SubstVec V) : List S -> List S
| [] => []
| x::xs => x[σ,] :: smap σ xs

instance [SubstMap S V] : SubstMap (List S) V where
  smap := List.smap

@[simp]
theorem List.smap_fix [SubstMap S V] {σ : SubstVec V} {l : List S} : smap σ l = l[σ,] := by
  simp only [SubstMap.smap]

@[simp]
theorem List.smap_nil [SubstMap S V] {σ : SubstVec V} : ([] : List S)[σ,] = [] := by
  simp only [SubstMap.smap, smap]

@[simp]
theorem List.smap_cons [SubstMap S V] {σ : SubstVec V} {x} {xs : List S}
  : (x::xs)[σ,] = x[σ,]::xs[σ,]
:= by simp only [SubstMap.smap, smap]

instance [SubstMap S V] [SubstMapId S V] : SubstMapId (List S) V where
  id_law := by intro s; induction s <;> simp [*]

instance [RenMap S V] [SubstMap S V] [SubstMapRenCompLeft S V]
  : SubstMapRenCompLeft (List S) V
where
  compose_left_law := by intro s; induction s <;> simp [*]

instance [RenMap S V] [RenMapAll V] [SubstMap S V] [SubstMapRenCompRight S V]
  : SubstMapRenCompRight (List S) V
where
  compose_right_law := by intro s; induction s <;> simp [*]

instance [SubstMap S V] [SubstMapAll V] [SubstMapComp S V] : SubstMapComp (List S) V where
  compose_law := by intro s; induction s <;> simp [*]

instance [RenMap S V] [SubstMap S V] [SubstMapStable S V] : SubstMapStable (List S) V where
  stable := by
    intro r σ h; funext; case _ l =>
    induction l <;> simp [*]
    rw [Subst.stable h]

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
theorem Ren.compose_sub_add_ren {r : Ren T} {k} : add T k >> sub T k >> r = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, compose]

@[simp]
theorem Subst.compose_left_sub_add_ren [RenMap T (T::V)] {r : RenVec (T::V)} {k}
  : Ren.add T k >> sub T k >> r = r.head.to
:= by
  simp [HAndThen.hAndThen, sub, compose_left, compose_right]
  ext; simp [RenVec.head, Ren.to]

@[simp]
theorem Subst.compose_right_sub_add_ren [RenMap T (T::V)] {r1 : RenVec V} {r2 : RenVec (T::V)} {k}
  : add T k >> (.sub T k .: r1) >> r2 = r2.head.to
:= by
  cases r2; case _ r2 r2s =>
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose_right]
  ext; simp [RenVec.head, Ren.sub, Ren.to, RenVec.compose]

@[simp]
theorem Subst.compose_sub_add_ren [RenMapAll (T::V)] [SubstMap T (T::V)]
  {σ : SubstVec V} {r2 : RenVec (T::V)} {k}
  : add T k >> (sub T k .: σ) >> r2 = r2.head.to
:= by
  cases r2; case _ r2 r2s =>
  simp [HAndThen.hAndThen, sub, add, compose, SubstVec.compose_right, compose_right]
  ext; simp [Ren.to]

@[simp]
theorem Ren.compose_sub_add_subst {σ : Subst T} {k} : add T k >> sub T k >> σ = σ := by
  simp [HAndThen.hAndThen, sub, add, Subst.compose_left]

@[simp]
theorem Subst.compose_left_sub_add_subst [SubstMap T (T::V)] {σ : SubstVec (T::V)} {k}
  : Ren.add T k >> sub T k >> σ = σ.head
:= by simp [HAndThen.hAndThen, sub, compose_left, compose]

@[simp]
theorem Subst.compose_right_sub_add_subst [SubstMap T (T::V)]
  {r1 : RenVec V} {σ : SubstVec (T::V)} {k}
  : add T k >> (.sub T k .: r1) >> σ = σ.head
:= by
  cases σ; case _ σ σs =>
  simp [HAndThen.hAndThen, add, SubstVec.compose_left, compose, compose_left]

@[simp]
theorem Subst.compose_sub_add_subst [SubstMapAll (T::V)]
  {σ : SubstVec V} {τ : SubstVec (T::V)} {k}
  : add T k >> (sub T k .: σ) >> τ = τ.head
:= by
  cases τ; case _ τ τs =>
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, compose, SubstVec.compose]

@[simp]
theorem Ren.compose_add_add {n m} : add T n >> add T m = add T (n + m) := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose]; grind

@[simp]
theorem RenVec.compose_add_add [RenMap T (T::V)] {r : Ren T} {rs : RenVec V} {n m}
  : Subst.add T n >> (Ren.add T m >> r) .: rs = Subst.add T (n + m) >> r .: rs
:= by
  simp [HAndThen.hAndThen, AndThen.andThen, Ren.compose, Subst.compose_right]; grind

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
theorem SubstVec.compose_add_add [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V} {n m}
  : Subst.add T n >> (Ren.add T m >> σ) .: σs = Subst.add T (n + m) >> σ .: σs
:= by
  simp [HAndThen.hAndThen, Subst.compose, Subst.compose_left]; grind

@[simp]
theorem Ren.compose_add_add_ren {r : Ren T} {n m}
  : add T n >> add T m >> r = add T (n + m) >> r
:= by simp [HAndThen.hAndThen, AndThen.andThen, add, compose]; grind

@[simp]
theorem Subst.compose_left_add_add_ren [RenMap T (T::V)] {r : RenVec (T::V)} {n m}
  : Ren.add T n >> add T m >> r = add T (n + m) >> r
:= by
  simp [HAndThen.hAndThen, add, compose_left, compose_right]; grind

@[simp]
theorem Subst.compose_right_add_add_ren [RenMap T (T::V)] {r1 : RenVec V} {r2 : RenVec (T::V)} {n m}
  : add T n >> (.add T m .: r1) >> r2 = add T (n + m) >> r2
:= by
  cases r2; case _ r2 r2s =>
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose_right, RenVec.compose, Ren.compose]
  grind

@[simp]
theorem Subst.compose_add_add_ren [RenMapAll (T::V)] [SubstMap T (T::V)]
  {σ : SubstVec V} {r : RenVec (T::V)} {n m}
  : add T n >> (add T m .: σ) >> r = add T (n + m) >> r
:= by
  cases r; case _ r rs =>
  simp [HAndThen.hAndThen, add, compose, SubstVec.compose_right, compose_right]
  grind

@[simp]
theorem Ren.compose_add_add_subst {σ : Subst T} {n m}
  : add T n >> add T m >> σ = add T (n + m) >> σ
:= by simp [HAndThen.hAndThen, add, Subst.compose_left]; grind

@[simp]
theorem Subst.compose_left_add_add_subst [RenMap T (T::V)] [SubstMap T (T::V)]
  {σ : SubstVec (T::V)} {n m}
  : Ren.add T n >> add T m >> σ = add T (n + m) >> σ
:= by
  cases σ; case _ σ σs =>
  simp [HAndThen.hAndThen, add, compose_left, compose]
  grind

@[simp]
theorem Subst.compose_right_add_add_subst [RenMap T (T::V)] [SubstMap T (T::V)]
  {r : RenVec V} {σ : SubstVec (T::V)} {n m}
  : add T n >> (.add T m .: r) >> σ = add T (n + m) >> σ
:= by
  cases σ; case _ σ σs =>
  simp [HAndThen.hAndThen, add, SubstVec.compose_left, compose_left, compose]
  grind

@[simp]
theorem Subst.compose_add_add_subst [SubstMapAll (T::V)]
  {σ : SubstVec V} {τ : SubstVec (T::V)} {n m}
  : add T n >> (add T m .: σ) >> τ = add T (n + m) >> τ
:= by
  cases τ; case _ τ τs =>
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose, SubstVec.compose]
  grind

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

-- TODO: the sub_sub_ren and sub_sub_subst variants

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
theorem SubstVec.compose_right_cons [RenMapAll (T::V)] :
  ∀ {σ1 : Subst T} {σ1s : SubstVec V} {r2s : RenVec (T::V)},
  (σ1 .: σ1s) >> r2s = (σ1 >> r2s) .: (σ1s >> r2s.tail)
| σ1, σ1s, .cons r2 r2s => by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem SubstVec.compose_cons
  [SubstMapAll (T::V)] {σ1 : Subst T} {σ1s : SubstVec V} : ∀ {σ2s : SubstVec (T::V)},
  (σ1 .: σ1s) >> σ2s = (σ1 >> σ2s) .: (σ1s >> σ2s.tail)
| cons r2 r2s => by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_append {r1 r2 : Ren T} : ∀ {l}, (l ++ r1) >> r2 = r2.actl l ++ (r1 >> r2)
| [] => by simp
| _::_ => by simp [compose_append]

@[simp]
theorem Subst.compose_left_append {r : Ren T} {τ : Subst T}
  : ∀ {l}, (l ++ r) >> τ = τ.actl l ++ (r >> τ)
| [] => by simp
| _::_ => by simp [compose_left_append]

@[simp]
theorem Subst.compose_right_append_list [RenMap T (T::V)] {σ : Subst T} {r : RenVec (T::V)}
  : ∀ {l}, (l ++ σ) >> r = r.head.actl l ++ (σ >> r)
| [] => by simp
| _::_ => by simp [compose_right_append_list]

@[simp]
theorem Subst.compose_right_append [RenMap T (T::V)] {σ : Subst T} {r : RenVec (T::V)}
  : ∀ {l : List (Action T)}, (l ++ σ) >> r = l⟨r,⟩ ++ (σ >> r)
| [] => by simp
| _::_ => by simp [compose_right_append]

@[simp]
theorem Subst.compose_append_list [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)}
  : ∀ {l}, (l ++ σ) >> τ = τ.head.actl l ++ (σ >> τ)
| [] => by simp
| _::_ => by simp [compose_append_list]

@[simp]
theorem Subst.compose_append [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)}
  : ∀ {l : List (Action T)}, (l ++ σ) >> τ = l[τ,] ++ (σ >> τ)
| [] => by simp
| _::_ => by simp [compose_append]

@[simp]
theorem Ren.compose_append_range {r1 r2 : Ren T} {s e}
  : ((s...e) ++ r1) >> r2 = r2.actr s e ++ (r1 >> r2)
:= by
  have lem := @compose_append _ r1 r2 (List.range' s (e - s))
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_left_append_range {r : Ren T} {τ : Subst T} {s e}
  : ((s...e) ++ r) >> τ = τ.actr s e ++ (r >> τ)
:= by
  have lem := @compose_left_append _ r τ (List.range' s (e - s))
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_right_append_range [RenMap T (T::V)] {σ : Subst T} {r : RenVec (T::V)} {s e}
  : ((s...e) ++ σ) >> r = r.head.actr s e ++ (σ >> r)
:= by
  have lem := @compose_right_append_list _ _ _ σ r (List.range' s (e - s))
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_append_range [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec (T::V)} {s e}
  : ((s...e) ++ σ) >> τ = τ.head.actr s e ++ (σ >> τ)
:= by
  have lem := @compose_append_list _ _ _ σ τ (List.range' s (e - s))
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Ren.compose_id_left {r : Ren T} : 𝐫0 >> r = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem RenVec.compose_id_left : ∀ {V : List (Type u2)} {r : RenVec V}, id V >> r = r
| [], nil => by simp [id]
| V::Vs, cons r rs => by simp [-cons_id, id, compose_id_left]

@[simp]
theorem Subst.compose_left_id_left {σ : Subst T} : 𝐫0(T) >> σ = σ := by
  simp [HAndThen.hAndThen, compose_left]

@[simp]
theorem Subst.compose_right_id_left [RenMap T (T::V)] {r : RenVec (T::V)}
  : 𝐬0(T) >> r = r.head.to
:= by simp [HAndThen.hAndThen, compose_right]; congr

@[simp]
theorem Subst.compose_id_left [SubstMap T (T::V)] {σ : SubstVec (T::V)}
  : 𝐬0(T) >> σ = σ.head
:= by simp [HAndThen.hAndThen, compose]

@[simp]
theorem SubstVec.compose_left_id_left : ∀ {V} {σ : SubstVec V}, RenVec.id V >> σ = σ
| [], nil => by simp
| _::Vs, cons σ σs =>
  have ih := compose_left_id_left (V := Vs) (σ := σs)
  by simp [-RenVec.cons_id, RenVec.id, ih]

@[simp]
theorem SubstVec.compose_right_id_left  : ∀ {V} [RenMapAll V] {r : RenVec V}, id V >> r = r.to
| [], _, .nil => by simp [RenVec.to]
| _::Vs, RenMapAll.cons _, .cons r rs =>
  have ih := compose_right_id_left (V := Vs) (r := rs)
  by simp [-cons_id, id, ih, RenVec.to]

@[simp]
theorem SubstVec.compose_id_left  : ∀ {V} [SubstMapAll V] {σ : SubstVec V}, id V >> σ = σ
| [], _, nil => by simp
| _::Vs, _, cons σ σs =>
  have ih := compose_id_left (V := Vs) (σ := σs)
  by simp [-cons_id, id, ih]

@[simp]
theorem Ren.compose_id_right {r : Ren T} : r >> 𝐫0 = r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose, id]

@[simp]
theorem RenVec.compose_id_right : ∀ {V} {r : RenVec V}, r >> id V = r
| [], nil => by simp
| _::_, cons r rs => by simp [-cons_id, id, compose_id_right]

@[simp]
theorem Subst.compose_left_id_right {r : Ren T} : r >> 𝐬0(T) = r.to := by
  simp [HAndThen.hAndThen, compose_left]; congr

@[simp]
theorem Subst.compose_right_id_right [RenMap T (T::V)] [RenMapId T (T::V)] {σ : Subst T}
  : σ >> RenVec.id (T::V) = σ
:= by simp [HAndThen.hAndThen, compose_right]

@[simp]
theorem Subst.compose_id_right [SubstMap T (T::V)] [SubstMapId T (T::V)] {σ : Subst T}
  : σ >> SubstVec.id (T::V) = σ
:= by simp [HAndThen.hAndThen, compose]

@[simp]
theorem SubstVec.compose_right_id_right : ∀ {V} [RenMapAll V] [RenMapLaws V] {σ : SubstVec V},
  σ >> RenVec.id V = σ
| [], _, _, .nil => by simp
| _::_, _, _, .cons σ σs =>
  have ih := @compose_right_id_right _ _ _ σs
  by simp [-RenVec.cons_id, RenVec.id, ih]; simp

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
theorem Subst.compose_assoc_srr [RenMapAll (T::V)] [RenMapComp T (T::V)]
  {s1 : Subst T} {r2 : RenVec (T::V)} {r3 : RenVec (T::V)}
  : (s1 >> r2) >> r3 = s1 >> r2 >> r3
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose_right]

@[simp]
theorem Subst.compose_assoc_srs
  [RenMapAll (T::V)] [SubstMapAll (T::V)] [SubstMapRenCompLeft T (T::V)]
  {s1 : Subst T} {r2 : RenVec (T::V)} {s3 : SubstVec (T::V)}
  : (s1 >> r2) >> s3 = s1 >> r2 >> s3
:= by simp [HAndThen.hAndThen, compose_right, compose]

@[simp]
theorem Subst.compose_assoc_ssr
  [RenMapAll (T::V)] [SubstMapAll (T::V)] [SubstMapRenCompRight T (T::V)]
  {s1 : Subst T} {s2 : SubstVec (T::V)} {r3 : RenVec (T::V)}
  : (s1 >> s2) >> r3 = s1 >> s2 >> r3
:= by simp [HAndThen.hAndThen, compose_right, compose]

@[simp]
theorem Subst.compose_assoc [SubstMapAll (T::V)] [SubstMapComp T (T::V)]
  {s1 : Subst T} {s2 : SubstVec (T::V)} {s3 : SubstVec (T::V)}
  : (s1 >> s2) >> s3 = s1 >> s2 >> s3
:= by simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Ren.compose_add_cons {r : Ren T} {n k} : (add T (n + 1)) >> (k .: r) = add T n >> r := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]
  funext; case _ i =>
  rw [<-Nat.add_assoc]; simp

@[simp]
theorem Subst.compose_left_add_cons {σ : Subst T} {n k}
  : (Ren.add T (n + 1)) >> (k .: σ) = Ren.add T n >> σ
:= by
  simp [HAndThen.hAndThen, compose_left]
  funext; case _ i =>
  rw [<-Nat.add_assoc]; simp

@[simp]
theorem Subst.compose_right_add_cons [RenMap T (T::V)] {r : Ren T} {rs : RenVec V} {n k}
  : (add T (n + 1)) >> (k .: r) .: rs = add T n >> r .: rs
:= by
  simp [HAndThen.hAndThen, compose_right]
  funext; case _ i =>
  rw [<-Nat.add_assoc]; simp

@[simp]
theorem Subst.compose_add_cons [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V} {n k}
  : (add T (n + 1)) >> (k .: σ) .: σs = add T n >> σ .: σs
:= by
  simp [HAndThen.hAndThen, compose]
  funext; case _ i =>
  rw [<-Nat.add_assoc]; simp

@[simp]
theorem Ren.compose_add_append {r : Ren T}
  : ∀ {n} {l : List Nat}, n ≥ l.length -> (add T n) >> (l ++ r) = add T (n - l.length) >> r
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_add_append h]

@[simp]
theorem Subst.compose_left_add_append_list {σ : Subst T}
  : ∀ {n} {l : List Nat}, n ≥ l.length -> (Ren.add T n) >> (l ++ σ) = Ren.add T (n - l.length) >> σ
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_left_add_append_list h]

@[simp]
theorem Subst.compose_left_add_append {σ : Subst T}
  : ∀ {n} {l : List (Action T)}, n ≥ l.length ->
    (Ren.add T n) >> (l ++ σ) = Ren.add T (n - l.length) >> σ
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_left_add_append h]

@[simp]
theorem Subst.compose_right_add_append [RenMap T (T::V)] {r :Ren T} {rs :RenVec V}
  : ∀ {n} {l : List Nat}, n ≥ l.length ->
    (add T n) >> (l ++ r) .: rs = add T (n - l.length) >> r .: rs
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_right_add_append h]

@[simp]
theorem Subst.compose_add_append_list [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V}
  : ∀ {n} {l : List Nat}, n ≥ l.length ->
    (add T n) >> (l ++ σ) .: σs = add T (n - l.length) >> σ .: σs
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_add_append_list h]

@[simp]
theorem Subst.compose_add_append [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V}
  : ∀ {n} {l : List (Action T)}, n ≥ l.length ->
    (add T n) >> (l ++ σ) .: σs = add T (n - l.length) >> σ .: σs
| _, [], _ => by simp
| n + 1, x::xs, h =>
  have h : n ≥ xs.length := by grind
  by simp [compose_add_append h]

@[simp]
theorem Ren.compose_add_append_range {r : Ren T} {n s e : Nat} (h : n ≥ (e - s))
  : (add T n) >> ((s...e) ++ r) = add T (n - (e - s)) >> r
:= by
  have lem := @compose_add_append _ r n (List.range' s (e - s)) (by simp; grind)
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_left_add_append_range {σ : Subst T} {n s e : Nat} (h : n ≥ (e - s))
  : (Ren.add T n) >> ((s...e) ++ σ) = Ren.add T (n - (e - s)) >> σ
:= by
  have lem := @compose_left_add_append_list _ σ n (List.range' s (e - s)) (by simp; grind)
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_right_add_append_range [RenMap T (T::V)] {r : Ren T} {rs : RenVec V}
  {n s e : Nat} (h : n ≥ (e - s))
  : (add T n) >> ((s...e) ++ r) .: rs = add T (n - (e - s)) >> r .: rs
:= by
  have lem := @compose_right_add_append _ _ _ r rs n (List.range' s (e - s)) (by simp; grind)
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Subst.compose_add_append_range [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V}
  {n s e : Nat} (h : n ≥ (e - s))
  : (add T n) >> ((s...e) ++ σ) .: σs = add T (n - (e - s)) >> σ .: σs
:= by
  have lem := @compose_add_append_list _ _ _ σ σs n (List.range' s (e - s)) (by simp; grind)
  simp [HAppend.hAppend]; simp [HAppend.hAppend] at lem
  rw [lem]

@[simp]
theorem Ren.cons_add_compose {r : Ren T} : r.act 0 .: (add T 1 >> r) =  r := by
  simp [AltCons.altCons, HAndThen.hAndThen, AndThen.andThen, compose, cons]
  cases r; case _ f =>
  congr; funext; case _ i =>
  cases i <;> simp

@[simp]
theorem Subst.cons_add_compose_left {σ : Subst T} : σ.act 0 .: (Ren.add T 1 >> σ) = σ := by
  simp [AltCons.altCons, HAndThen.hAndThen, compose_left, cons]
  cases σ; case _ f =>
  congr; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.cons_add_compose_left_to {r : Ren T} : re (r.act 0) .: (Ren.add T 1 >> r.to) = r.to
:= by
  simp [AltCons.altCons, HAndThen.hAndThen, compose_left, cons]
  cases r; case _ f =>
  congr; funext; case _ x =>
  cases x <;> simp [Ren.to]

@[simp]
theorem Subst.cons_add_compose_right [RenMap T (T::V)] {r : Ren T} {rs : RenVec V}
  : re (r.act 0) .: (add T 1 >> r .: rs) = r.to
:= by
  simp [AltCons.altCons, HAndThen.hAndThen, compose_right, cons]
  cases r; case _ f =>
  congr; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Subst.cons_add_compose [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V}
  : σ.act 0 .: (add T 1 >> σ .: σs) = σ
:= by
  simp [AltCons.altCons, HAndThen.hAndThen, compose, cons]
  cases σ; case _ f =>
  congr; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Ren.append_range_actr_lt {r : Ren T} {k s e} (h : e ≤ k)
  : ((0...k) ++ r).actr s e = List.range' s (e - s)
:= by
  simp [actr]; generalize ndef : e - s = n
  induction n generalizing e s k; simp; case _ n ih =>
  have lem : e - (s + 1) = n := by grind
  simp [List.range'_succ, ih h lem]
  cases Nat.decLt s k
  case _ h2 => exfalso; grind
  case _ h2 => rw [Ren.append_range_act_lt h2]; simp

@[simp]
theorem Subst.append_range_actr_lt {σ : Subst T} {k s e} (h : e ≤ k)
  : ((0...k) ++ σ).actr s e = List.map re (List.range' s (e - s))
:= by
  simp [actr]; intro i h1 h2
  rw [Subst.append_range_act_lt] <;> simp; grind

@[simp]
theorem Ren.to_id : (id T).to = .id T := by simp [to, Subst.id]

@[simp]
theorem Ren.to_add {k} : (add T k).to = .add T k := by simp [to, Subst.add]

@[simp]
theorem Ren.to_sub {k} : (sub T k).to = .sub T k := by simp [to, Subst.sub]

@[simp]
theorem Ren.to_cons {n} {r : Ren T} : (n .: r).to = re n .: r.to := by
  simp [to]; congr; funext; case _ x =>
  cases x <;> simp

@[simp]
theorem Ren.to_append {l : List Nat} {r : Ren T} : (l ++ r).to = l ++ r.to := by
  induction l <;> simp [*]

@[simp]
theorem Ren.to_append_range {s e : Nat} {r : Ren T} : ((s...e) ++ r).to = (s...e) ++ r.to := by
  rw [<-append_list_to_range, to_append]; simp

@[simp]
theorem Ren.to_compose {r1 r2 : Ren T} : (r1 >> r2).to = r1 >> r2.to := by
  simp [HAndThen.hAndThen, AndThen.andThen, to, compose, Subst.compose_left]

@[simp]
theorem RenVec.to_cons {r : Ren T} {rs : RenVec V} : (r .: rs).to = r.to .: rs.to := by
  simp [RenVec.to]

@[simp]
theorem Subst.to_compose_left
  [RenMap T (T::V)] [SubstMap T (T::V)] {r : Ren T} {σ : SubstVec (T::V)}
  : r.to >> σ = r >> σ.head
:= by
  simp [HAndThen.hAndThen, compose, compose_left]; funext; case _ x =>
  cases σ; case _ σ σs =>
  simp [Ren.to]

@[simp]
theorem Subst.to_compose_right
  [RenMap T (T::V)] [SubstMap T (T::V)] [SubstMapStable T (T::V)] {σ : Subst T} {r : RenVec (T::V)}
  : σ >> r.to = σ >> r
:= by
  simp [HAndThen.hAndThen, compose, compose_right]; funext; case _ x =>
  cases r; case _ r rs =>
  simp
  have lem := @Subst.stable T (T::V) _ _ _ (r .: rs) (r.to .: rs.to) (by simp)
  rw [Subst.stable (r := r .: rs) (σ := r.to .: rs.to)]; simp

private theorem Ren.actr_add_fused_add {r : Ren T} {k s n x}
  : actr_add_fused (add T x >> r) k s n = actr_add_fused r (k + x) (s + x) n
:= by
  induction n generalizing k s x; simp [actr_add_fused]; case _ n ih =>
  simp [actr_add_fused, *]; congr 2; omega

private theorem Subst.actr_add_fused_left_add {σ : Subst T} {k s n x}
  : actr_add_fused_left (Ren.add T x >> σ) k s n = actr_add_fused_left σ (k + x) (s + x) n
:= by
  induction n generalizing k s x; simp [actr_add_fused_left]; case _ n ih =>
  simp [actr_add_fused_left, *]; congr 2; omega

private theorem Subst.actr_add_fused_right_add [RenMap T (T::V)]
  {r : Ren T} {rs : RenVec V} {k s n x}
  : actr_add_fused_right ((Ren.add T x >> r) .: rs) k s n
    = actr_add_fused_right (r.:rs) (k + x) (s + x) n
:= by
  induction n generalizing k s x; simp [actr_add_fused_right]; case _ n ih =>
  simp [actr_add_fused_right, *]; congr 2; omega

private theorem Subst.actr_add_fused_add [SubstMap T (T::V)]
  {σ : Subst T} {σs : SubstVec V} {k s n x}
  : actr_add_fused ((Ren.add T x >> σ) .: σs) k s n
    = actr_add_fused (σ.:σs) (k + x) (s + x) n
:= by
  induction n generalizing k s x; simp [actr_add_fused]; case _ n ih =>
  simp [actr_add_fused, *]; congr 2; omega

private theorem Ren.actr_add_fused_id {r : Ren T} {k}
  : actr_add_fused r k 0 k = r
:= by
  induction k generalizing r; simp [actr_add_fused]; case _ k ih =>
  simp [actr_add_fused]
  replace ih := @ih (add T 1 >> r)
  rw [actr_add_fused_add] at ih; simp at ih
  rw [ih]; rw [cons_add_compose]

private theorem Subst.actr_add_fused_left_id {σ : Subst T} {k}
  : actr_add_fused_left σ k 0 k = σ
:= by
  induction k generalizing σ; simp [actr_add_fused_left]; case _ k ih =>
  simp [actr_add_fused_left]
  replace ih := @ih (Ren.add T 1 >> σ)
  rw [actr_add_fused_left_add] at ih; simp at ih
  rw [ih]; rw [cons_add_compose_left]

private theorem Subst.actr_add_fused_right_id [RenMap T (T::V)] {r : Ren T} {rs : RenVec V} {k}
  : actr_add_fused_right (r.:rs) k 0 k = r.to
:= by
  induction k generalizing r; simp [actr_add_fused_right]; case _ k ih =>
  simp [actr_add_fused_right]
  replace ih := @ih (Ren.add T 1 >> r)
  rw [actr_add_fused_right_add] at ih; simp at ih
  rw [ih]; rw [cons_add_compose_left_to]

private theorem Subst.actr_add_fused_id [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V} {k}
  : actr_add_fused (σ.:σs) k 0 k = σ
:= by
  induction k generalizing σ; simp [actr_add_fused]; case _ k ih =>
  simp [actr_add_fused]
  replace ih := @ih (Ren.add T 1 >> σ)
  rw [actr_add_fused_add] at ih; simp at ih
  rw [ih]; simp

private theorem Ren.actr_add_fused_eq {r : Ren T} {k s n}
  : actr_add_fused r k s n = r.actr s (s + n) ++ (add T k >> r)
:= by
  induction n generalizing r k s; simp [actr_add_fused]; case _ n ih =>
  simp [actr]
  simp [actr_add_fused, actr, List.range'_succ, *]

private theorem Subst.actr_add_fused_left_eq {σ : Subst T} {k s n}
  : actr_add_fused_left σ k s n = σ.actr s (s + n) ++ (Ren.add T k >> σ)
:= by
  induction n generalizing σ k s; simp [actr_add_fused_left]; case _ n ih =>
  simp [actr]
  simp [actr_add_fused_left, actr, List.range'_succ, *]

private theorem Subst.actr_add_fused_right_eq [RenMap T (T::V)] {r : Ren T} {rs : RenVec V} {k s n}
  : actr_add_fused_right (r.:rs) k s n = r.actr s (s + n) ++ (add T k >> r .: rs)
:= by
  induction n generalizing r k s; simp [actr_add_fused_right]; case _ n ih =>
  simp [Ren.actr]
  simp [actr_add_fused_right, Ren.actr, List.range'_succ, *]

private theorem Subst.actr_add_fused_eq [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V} {k s n}
  : actr_add_fused (σ.:σs) k s n = σ.actr s (s + n) ++ (add T k >> σ .: σs)
:= by
  induction n generalizing σ k s; simp [actr_add_fused]; case _ n ih =>
  simp [actr, actr_add_fused, List.range'_succ, *]

@[simp]
theorem Ren.append_add_compose_range {r : Ren T} {k} : r.actr 0 k ++ (add T k >> r) = r := by
  have lem := @actr_add_fused_eq _ r k 0 k; simp at lem
  rw [<-lem, actr_add_fused_id]

@[simp]
theorem Subst.append_add_compose_left_range {σ : Subst T} {k}
  : σ.actr 0 k ++ (Ren.add T k >> σ) = σ
:= by
  have lem := @actr_add_fused_left_eq _ σ k 0 k; simp at lem
  rw [<-lem, actr_add_fused_left_id]

@[simp]
theorem Subst.append_add_compose_right_range [RenMap T (T::V)] {r : Ren T} {rs : RenVec V} {k}
  : r.actr 0 k ++ (add T k >> r .: rs) = r.to
:= by
  have lem := @actr_add_fused_right_eq _ _ _ r rs k 0 k; simp at lem
  rw [<-lem, actr_add_fused_right_id]

@[simp]
theorem Subst.append_add_compose_range [SubstMap T (T::V)] {σ : Subst T} {σs : SubstVec V} {k}
  : σ.actr 0 k ++ (add T k >> σ .: σs) = σ
:= by
  have lem := @actr_add_fused_eq _ _ _ σ σs k 0 k; simp at lem
  rw [<-lem, actr_add_fused_id]

theorem Ren.lift_act_lt {r : Ren T} {k i} (h : i < k)
  : (r.lift k).act i = i
:= by simp [lift]; grind

theorem Subst.lift_act_lt [RenMap T (T::V)] {σ : Subst T} {k i} (h : i < k)
  : (σ.lift V k).act i = re i
:= by simp [lift]; grind

theorem Ren.lift_act_ge {r : Ren T} {k i} {h : i ≥ k}
  : (r.lift k).act i = r.act (i - k) + k
:= by simp [lift]; rw [Ren.append_range_act_ge h]; simp

theorem Subst.lift_act_ge [RenMap T (T::V)] {σ : Subst T} {k i} {h : i ≥ k}
  : (σ.lift V k).act i = (σ.act (i - k))⟨.add (T::V) [k],⟩
:= by simp [lift]; rw [Subst.append_range_act_ge h]; simp

@[simp high]
theorem Ren.lift_id : ∀ {k}, (id T).lift k = id T := by simp [lift]

@[simp high]
theorem RenVec.lift_id : ∀ {V k}, (id V).lift k = id V
| [], _ => by simp [lift, id]
| _::_, [] => by simp [-cons_id, id, lift]
| _::_, _::_ => by simp [-cons_id, id, lift, lift_id]

@[simp high]
theorem Subst.lift_id [RenMap T (T::V)] {k} : (id T).lift V k = id T := by simp [lift]

@[simp high]
theorem SubstVec.lift_id : ∀ {V k} [RenMapAll V], (id V).lift k = id V
| [], _, _ => by simp [lift, id]
| _::_, [], _ => by simp [-cons_id, id, lift]
| V::Vs, k::ks, @RenMapAll.cons _ _ i _ => by simp [-cons_id, id, lift, lift_id]

@[simp]
theorem RenVec.lift_empty : ∀ {V} {r : RenVec V}, r.lift [] = r
| [], nil => by simp
| _::_, cons r rs => by simp [lift]

@[simp]
theorem SubstVec.lift_empty : ∀ {V} [RenMapAll V] {σ : SubstVec V}, σ.lift [] = σ
| [], .nil, nil => by simp
| _::_, _, cons r rs => by simp [lift]

@[simp]
theorem RenVec.lift_cons {r : Ren T} {rs : RenVec V} {x xs}
  : (r .: rs).lift (x::xs) = r.lift x .: rs.lift xs
:= by simp [lift]

@[simp]
theorem SubstVec.lift_cons [RenMapAll (T::V)] {σ : Subst T} {σs : SubstVec V} {x xs}
  : (σ .: σs).lift (x::xs) = σ.lift V x .: σs.lift xs
:= by simp [lift]

end

end LeanSubst
