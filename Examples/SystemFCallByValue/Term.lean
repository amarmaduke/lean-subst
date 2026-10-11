import LeanSubst
import LeanSubst.Automation.Basic

open LeanSubst

namespace SystemFCallByValue

inductive Ty where
| var : Nat -> Ty
| arrow : Ty -> Ty -> Ty
| all : Ty -> Ty
| nat : Ty

#leansubst var Ty.var
#leansubst bind Ty at pos 0 in Ty.all
#leansubst generate Ty

mutual
inductive Value where
| var (x : Nat) : Value
| lam (A : Ty) (t : Term) : Value
| tlam (t : Term) : Value

inductive Term where
| val (v : Value) : Term
| app (f a : Term) : Term
| tapp (f : Term) (A : Ty) : Term
end

@[coe]
def Value.from_action : Action Value -> Value
| re y => var y
| su t => t

@[simp, grind =]
theorem Value.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp, grind =]
theorem Value.from_action_succ {n k} : from_action ((Subst.add _ k).act n) = var (n + k) := by
  simp [from_action]

@[simp, grind =]
theorem Value.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp, grind =]
theorem Value.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Value) Value where
  coe := Value.from_action

mutual
@[simp]
def Value.rmap (r : RenVec [Value, Ty]) : Value -> Value
| .var x => .var (r.head.act x)
| .lam A t => .lam A⟨r.tail.head⟩ (t.rmap $ r.lift [1, 0])
| .tlam t => .tlam (t.rmap $ r.lift [0, 1])

@[simp]
def Term.rmap (r : RenVec [Value, Ty]) : Term -> Term
| .val v => .val (v.rmap r)
| .app f a => .app (f.rmap r) (a.rmap r)
| .tapp f A => .tapp (f.rmap r) A⟨r.tail.head⟩
end

@[reducible, simp]
instance instRenMapAll_Value_Ty : RenMapAll [Value, Ty] :=
  @RenMapAll.cons _ _ ⟨Value.rmap⟩ instRenMapAll_Ty

instance : RenMap Term [Value, Ty] where
  rmap := Term.rmap

@[simp]
theorem Value.rmap_fix {r : RenVec [Value, Ty]} {t : Value} : rmap r t = t⟨r,⟩ := by
  simp +instances [RenMap.rmap]

@[simp]
theorem Term.rmap_fix {r : RenVec [Value, Ty]} {t : Term} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Value.rmap_term_ty_var {x} {r : RenVec [Value, Ty]} : (var x)⟨r,⟩ = var (r.head.act x) := rfl

@[simp]
theorem Term.rmap_term_ty_app {t1 t2} {r : RenVec [Value, Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Value.rmap_term_ty_lam {A t} {r : RenVec [Value, Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.tail.head⟩ t⟨r.lift [1, 0],⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_tapp {t1 t2} {r : RenVec [Value, Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.tail.head⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_term_ty_tlam {t} {r : RenVec [Value, Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [0, 1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_val {t1} {r : RenVec [Value, Ty]}
  : (val t1)⟨r,⟩ = val t1⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.from_action_rmap {t : Action Value} {r : RenVec [Value, Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp [from_action]

mutual
  @[simp]
  theorem Value.rmap_id : ∀ {s : Value}, s⟨RenVec.id [Value, Ty],⟩ = s
  | .var x => by simp
  | .lam A t =>
    have ih := t.rmap_id
    by simp [*]
  | .tlam t =>
    have ih := t.rmap_id
    by simp [*]

  @[simp]
  theorem Term.rmap_id : ∀ {s : Term}, s⟨RenVec.id [Value, Ty],⟩ = s
  | .val v =>
    have ih := v.rmap_id
    by simp [*]
  | .app f a =>
    have ih1 := f.rmap_id
    have ih2 := a.rmap_id
    by simp [*]
  | .tapp f A =>
    have ih := f.rmap_id
    by simp [*]
end

instance : RenMapId Value [Value, Ty] where
  id_law := Value.rmap_id

instance : RenMapId Term [Value, Ty] where
  id_law := Term.rmap_id

mutual
  @[simp]
  theorem Value.rmap_compose : ∀ {s : Value} {r1 r2 : RenVec [Value, Ty]}, s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
  | .var x, _, _ => by simp
  | .lam A t, ·⟨r1, r2⟩, ·⟨r3, r4⟩ => by simp [Term.rmap_compose]
  | .tlam t, ·⟨r1, r2⟩, ·⟨r3, r4⟩ => by simp [Term.rmap_compose]

  @[simp]
  theorem Term.rmap_compose : ∀ {s : Term} {r1 r2 : RenVec [Value, Ty]}, s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
  | .val v, ·⟨r1, r2⟩, ·⟨r3, r4⟩ => by simp [Value.rmap_compose]
  | .app f a, ·⟨r1, r2⟩, ·⟨r3, r4⟩ => by simp [Term.rmap_compose]
  | .tapp f A, ·⟨r1, r2⟩, ·⟨r3, r4⟩ => by simp [Term.rmap_compose]
end

instance : RenMapComp Value [Value, Ty] where
  compose_law := Value.rmap_compose

instance : RenMapComp Term [Value, Ty] where
  compose_law := Term.rmap_compose

mutual
@[simp]
def Value.smap (σ : SubstVec [Value, Ty]) : Value -> Value
| .var x => σ.head.act x
| .lam A t => .lam A[σ.tail.head] (t.smap $ σ.lift [1, 0])
| .tlam t => .tlam (t.smap $ σ |> .lift [0, 1] |> .shift [[0, 1]])

@[simp]
def Term.smap (σ : SubstVec [Value, Ty]) : Term -> Term
| .val v => .val (v.smap σ)
| .app f a => .app (f.smap σ) (a.smap σ)
| .tapp f A => .tapp (f.smap σ) A[σ.tail.head]
end

@[reducible, simp]
instance : SubstMapAll [Value, Ty] :=
  @SubstMapAll.cons _ _ ⟨Value.smap⟩ instSubstMapAll_Ty

instance : SubstMap Term [Value, Ty] where
  smap := Term.smap

@[simp]
theorem Value.smap_fix {σ : SubstVec [Value, Ty]} {t : Value} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Term.smap_fix {σ : SubstVec [Value, Ty]} {t : Term} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Value.smap_term_ty_var {x} {σ : SubstVec [Value, Ty]} : (var x)[σ,] = σ.head.act x := rfl

@[simp]
theorem Term.smap_term_ty_app {t1 t2} {σ : SubstVec [Value, Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Value.smap_term_ty_lam {A t} {σ : SubstVec [Value, Ty]}
  : (lam A t)[σ,] = lam A[σ.tail.head] t[σ.lift [1, 0],]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_tapp {t1 t2} {σ : SubstVec [Value, Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.tail.head]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_term_ty_tlam {t} {σ : SubstVec [Value, Ty]}
  : (tlam t)[σ,] = tlam t[σ |> .lift [0, 1] |> .shift [[0, 1]],]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_val {t1} {σ : SubstVec [Value, Ty]}
  : (val t1)[σ,] = val t1[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.from_action_smap {t : Action Value} {σ : SubstVec [Value, Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp [from_action]

mutual
  @[simp]
  theorem Value.smap_id :  ∀ {s : Value}, s[.id [Value, Ty],] = s
  | .var x => by simp
  | .lam A t =>
    have ih := t.smap_id
    by simp [*]
  | .tlam t =>
    have ih := t.smap_id
    by simp [*]

  @[simp]
  theorem Term.smap_id :  ∀ {s : Term}, s[.id [Value, Ty],] = s
  | .val v =>
    have ih := v.smap_id
    by simp [*]
  | .app f a =>
    have ih := f.smap_id
    have ih := a.smap_id
    by simp [*]
  | .tapp f A =>
    have ih := f.smap_id
    by simp [*]
end

instance : SubstMapId Value [Value, Ty] where
  id_law := Value.smap_id

instance : SubstMapId Term [Value, Ty] where
  id_law := Term.smap_id

mutual
  @[simp]
  theorem Value.smap_ren_compose_left : ∀ {s : Value} {r : RenVec [Value, Ty]} {τ : SubstVec [Value, Ty]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .var x, r, τ => by simp
  | .lam A t, r, τ =>
    have ih1 := t.smap_ren_compose_left (r := r.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      repeat (cases r; case' _ r => try simp only)
      repeat (cases τ; case' _ τ => try simp only)
      simp [*] at *; congr
    }
  | .tlam t, r, τ =>
    have ih := t.smap_ren_compose_left
      (r := r.lift [0, 1])
      (τ := τ |> .lift [0, 1] |> .shift [[0, 1]])
    by {
      repeat (cases r; case' _ r => try simp only)
      repeat (cases τ; case' _ τ => try simp only)
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_left : ∀ {s : Term} {r : RenVec [Value, Ty]} {τ : SubstVec [Value, Ty]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .val v, r, τ =>
    have ih1 := v.smap_ren_compose_left (r := r) (τ := τ)
    by simp [*]
  | .app f a, r, τ =>
    have ih1 := f.smap_ren_compose_left (r := r) (τ := τ)
    have ih2 := a.smap_ren_compose_left (r := r) (τ := τ)
    by simp [*]
  | .tapp f A, r, τ =>
    have ih1 := f.smap_ren_compose_left (r := r) (τ := τ)
    by simp [*]
end

instance : SubstMapRenCompLeft Value [Value, Ty] where
  compose_left_law := Value.smap_ren_compose_left

instance : SubstMapRenCompLeft Term [Value, Ty] where
  compose_left_law := Term.smap_ren_compose_left

mutual
  @[simp]
  theorem Value.smap_ren_compose_right : ∀ {s : Value} {r : RenVec [Value, Ty]} {σ : SubstVec [Value, Ty]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .var x, r, σ => by simp
  | .lam A t, r, σ =>
    have ih1 := t.smap_ren_compose_right (r := r.lift [1, 0]) (σ := σ.lift [1, 0])
    by {
      repeat (cases r; case' _ r => try simp only)
      repeat (cases σ; case' _ σ => try simp only)
      simp [*] at *; congr
    }
  | .tlam t, r, σ =>
    have ih := t.smap_ren_compose_right
      (r := r.lift [0, 1])
      (σ := σ |> .lift [0, 1] |> .shift [[0, 1]])
    by {
      repeat (cases r; case' _ r => try simp only)
      repeat (cases σ; case' _ σ => try simp only)
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_right : ∀ {s : Term} {r : RenVec [Value, Ty]} {σ : SubstVec [Value, Ty]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .val v, r, σ =>
    have ih1 := v.smap_ren_compose_right (r := r) (σ := σ)
    by simp [*]
  | .app f a, r, σ =>
    have ih1 := f.smap_ren_compose_right (r := r) (σ := σ)
    have ih2 := a.smap_ren_compose_right (r := r) (σ := σ)
    by simp [*]
  | .tapp f A, r, σ =>
    have ih1 := f.smap_ren_compose_right (r := r) (σ := σ)
    by
      repeat (cases r; case' _ r => try simp only)
      repeat (cases σ; case' _ σ => try simp only)
      simp [*]
end

instance : SubstMapRenCompRight Value [Value, Ty] where
  compose_right_law := Value.smap_ren_compose_right

instance : SubstMapRenCompRight Term [Value, Ty] where
  compose_right_law := Term.smap_ren_compose_right

mutual
  @[simp]
  theorem Value.smap_compose : ∀ {s : Value} {σ τ : SubstVec [Value, Ty]}, s[σ,][τ,] = s[σ >> τ,]
  | .var x, σ, τ => by simp
  | .lam A t, σ, τ =>
    have ih1 := t.smap_compose (σ := σ.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      repeat (cases σ; case' _ σ => try simp only)
      repeat (cases τ; case' _ τ => try simp only)
      simp [*] at *; congr
    }
  | .tlam t, σ, τ =>
    have ih := t.smap_compose
      (σ := σ |> .lift [0, 1] |> .shift [[0, 1]])
      (τ := τ |> .lift [0, 1] |> .shift [[0, 1]])
    by {
      repeat (cases σ; case' _ σ => try simp only)
      repeat (cases τ; case' _ τ => try simp only)
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_compose : ∀ {s : Term} {σ τ : SubstVec [Value, Ty]}, s[σ,][τ,] = s[σ >> τ,]
  | .val v, σ, τ =>
    have ih1 := v.smap_compose (σ := σ) (τ := τ)
    by simp [*]
  | .app f a, σ, τ =>
    have ih1 := f.smap_compose (σ := σ) (τ := τ)
    have ih2 := a.smap_compose (σ := σ) (τ := τ)
    by simp [*]
  | .tapp f A, σ, τ =>
    have ih1 := f.smap_compose (σ := σ) (τ := τ)
    by
      repeat (cases σ; case' _ σ => try simp only)
      repeat (cases τ; case' _ τ => try simp only)
      simp [*]
end

instance : SubstMapComp Value [Value, Ty] where
  compose_law := Value.smap_compose

instance : SubstMapComp Term [Value, Ty] where
  compose_law := Term.smap_compose

end SystemFCallByValue
