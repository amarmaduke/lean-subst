module

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
theorem Ren.compose_action {r1 r2 : Ren T} {x} : (r1 >> r2).act x = r2.act (r1.act x) := by
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem Subst.compose_action [SubstMap T (T::V)] {σ : Subst T} {τ : SubstVec $ T::V} {x : Nat}
  : (σ >> τ).act x = (σ.act x)[τ,]
:= by simp [HAndThen.hAndThen, compose, act, SubstAction.act]

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
theorem Ren.compose_sub_add {k} : add T k >> sub T k = id T := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, add, id, compose]

@[simp]
theorem Ren.compose_add_add {n m} : add T n >> add T m = add T (n + m) := by
  simp [HAndThen.hAndThen, AndThen.andThen, add, compose]; grind

@[simp]
theorem Ren.compose_sub_sub {n m} : sub T n >> sub T m = sub T (n + m) := by
  simp [HAndThen.hAndThen, AndThen.andThen, sub, compose]; grind

@[simp]
theorem RenVec.compose_head {σ τ : RenVec (T::V)} : (σ >> τ).head = σ.head >> τ.head := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]

@[simp]
theorem RenVec.compose_tail {σ τ : RenVec (T::V)} : (σ >> τ).tail = σ.tail >> τ.tail := by
  rcases σ with ⟨σ, σ'⟩
  rcases τ with ⟨τ, τ'⟩
  simp [HAndThen.hAndThen, AndThen.andThen, compose]




end LeanSubst
