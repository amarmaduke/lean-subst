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
theorem Value.from_action_succ {n} : from_action (𝐬1.act n) = var (n + 1) := by
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
| .var x => .var (r.1.act x)
| .lam A t => .lam A⟨r.2.1⟩ (t.rmap $ r.lift [1, 0])
| .tlam t => .tlam (t.rmap $ r.lift [0, 1])

@[simp]
def Term.rmap (r : RenVec [Value, Ty]) : Term -> Term
| .val v => .val (v.rmap r)
| .app f a => .app (f.rmap r) (a.rmap r)
| .tapp f A => .tapp (f.rmap r) A⟨r.2.1⟩
end

instance : RenMap Value [Value, Ty] where
  rmap := Value.rmap

instance : RenMap Term [Value, Ty] where
  rmap := Term.rmap

@[simp]
theorem Value.rmap_fix {r : RenVec [Value, Ty]} {t : Value} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_fix {r : RenVec [Value, Ty]} {t : Term} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Value.rmap_term_ty_var {x} {r : RenVec [Value, Ty]} : (var x)⟨r,⟩ = var (r.1.act x) := rfl

@[simp]
theorem Term.rmap_term_ty_app {t1 t2} {r : RenVec [Value, Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Value.rmap_term_ty_lam {A t} {r : RenVec [Value, Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.2.1⟩ t⟨r.lift [1, 0],⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_tapp {t1 t2} {r : RenVec [Value, Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.2.1⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_term_ty_tlam {t} {r : RenVec [Value, Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [0, 1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_val {t1} {r : RenVec [Value, Ty]}
  : (val t1)⟨r,⟩ = val t1⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

instance : RenSuffix Value [Ty] := ⟨⟩
instance : RenMap Value [Ty] where
  rmap r := Value.rmap (Ren.id Value, r.1, .nil)

instance : RenSuffix Term [Ty] := ⟨⟩
instance : RenMap Term [Ty] where
  rmap r := Term.rmap (Ren.id Value, r.1, .nil)

@[simp]
theorem Value.rmap_ty_var {x} {r : RenVec [Ty]} : (var x)⟨r,⟩ = var x := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_ty_app {t1 t2} {r : RenVec [Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_ty_lam {A t} {r : RenVec [Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.1⟩ t⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_ty_tapp {t1 t2} {r : RenVec [Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.1⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_ty_tlam {t} {r : RenVec [Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_ty_val {t1} {r : RenVec [Ty]}
  : (val t1)⟨r,⟩ = val t1⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

instance : RenMap Value [Value] where
  rmap r := Value.rmap (r.1, Ren.id Ty, .nil)

instance : RenMap Term [Value] where
  rmap r := Term.rmap (r.1, Ren.id Ty, .nil)

@[simp]
theorem Value.rmap_term_var {x} {r : RenVec [Value]} : (var x)⟨r,⟩ = var (r.1.act x) := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_app {t1 t2} {r : RenVec [Value]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_term_lam {A t} {r : RenVec [Value]}
  : (lam A t)⟨r,⟩ = lam A t⟨r.lift [1],⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_tapp {t1 t2} {r : RenVec [Value]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.rmap_term_tlam {t} {r : RenVec [Value]} : (tlam t)⟨r,⟩ = tlam t⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_val {t1} {r : RenVec [Value]}
  : (val t1)⟨r,⟩ = val t1⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Value.from_action_rmap {t : Action Value} {r : RenVec [Value, Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp [from_action]

@[simp]
theorem Value.from_action_rmap0 {t : Action Value} {r : RenVec [Value]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp [from_action]

@[simp]
theorem Value.from_action_rmap1 {t : Action Value} {r : RenVec [Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp [from_action]

instance : RenSuffix Value [] := ⟨⟩
instance : RenMap Value [] where
  rmap _ := id

instance : RenSuffix Term [] := ⟨⟩
instance : RenMap Term [] where
  rmap _ := id

@[reducible, simp]
instance instRenMapAll_Value : RenMapAll [Value] := .cons .nil

@[reducible, simp]
instance instRenMapAll_Value_Ty : RenMapAll [Value, Ty] := .cons instRenMapAll_Ty

instance : RenMapEmpty Value where
  apply_empty := by intro s; simp [RenMap.rmap]

instance : RenMapEmpty Term where
  apply_empty := by intro s; simp [RenMap.rmap]

mutual
  theorem Value.rmap_vecdef : ∀ {s : Value} {r : RenVec [Value, Ty]}, s⟨r,⟩ = s⟨r.2,⟩⟨r.1⟩
  | .var x, _ => by simp
  | .lam A t, r =>
    have ih := t.rmap_vecdef (r := r.lift [1, 0])
    by simp [*]
  | .tlam t, r =>
    have ih := t.rmap_vecdef (r := r.lift [0, 1])
    by simp [*]

  theorem Term.rmap_vecdef : ∀ {s : Term} {r : RenVec [Value, Ty]}, s⟨r,⟩ = s⟨r.2,⟩⟨r.1⟩
  | .val v, r =>
    have ih := v.rmap_vecdef (r := r)
    by simp [*]
  | .app f a, r =>
    have ih1 := f.rmap_vecdef (r := r)
    have ih2 := a.rmap_vecdef (r := r)
    by simp [*]
  | .tapp f A, r =>
    have ih := f.rmap_vecdef (r := r)
    by simp [*]
end

instance : RenMapVecDef Value Value [Ty] where
  apply_vecdef := Value.rmap_vecdef

instance : RenMapVecDef Term Value [Ty] where
  apply_vecdef := Term.rmap_vecdef

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
  apply_id := Value.rmap_id

instance : RenMapId Term [Value, Ty] where
  apply_id := Term.rmap_id

mutual
  @[simp]
  theorem Value.rmap_compose : ∀ {s : Value} {r1 r2 : RenVec [Value, Ty]}, s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
  | .var x, _, _ => by simp
  | .lam A t, r1, r2 =>
    have ih := t.rmap_compose (r1 := r1.lift [1, 0]) (r2 := r2.lift [1, 0])
    by simp [*]
  | .tlam t, r1, r2 =>
    have ih := t.rmap_compose (r1 := r1.lift [0, 1]) (r2 := r2.lift [0, 1])
    by simp [*]

  @[simp]
  theorem Term.rmap_compose : ∀ {s : Term} {r1 r2 : RenVec [Value, Ty]}, s⟨r1,⟩⟨r2,⟩ = s⟨r1 >> r2,⟩
  | .val v, r1, r2 =>
    have ih := v.rmap_compose (r1 := r1) (r2 := r2)
    by simp [*]
  | .app f a, r1, r2 =>
    have ih1 := f.rmap_compose (r1 := r1) (r2 := r2)
    have ih2 := a.rmap_compose (r1 := r1) (r2 := r2)
    by simp [*]
  | .tapp f A, r1, r2 =>
    have ih := f.rmap_compose (r1 := r1) (r2 := r2)
    by simp [*]
end

instance : RenMapCompose Value [Value, Ty] where
  apply_compose := Value.rmap_compose

instance : RenMapCompose Term [Value, Ty] where
  apply_compose := Term.rmap_compose

instance : RenMapVecDef Value Value [] where
  apply_vecdef := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapVecDef Term Value [] where
  apply_vecdef := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapId Value [Value] where
  apply_id := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapId Term [Value] where
  apply_id := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapCompose Value [Value] where
  apply_compose := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapCompose Term [Value] where
  apply_compose := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapId Value [Ty] where
  apply_id := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapId Term [Ty] where
  apply_id := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapCompose Value [Ty] where
  apply_compose := by intro s; simp only [RenMap.rmap]; simp

instance : RenMapCompose Term [Ty] where
  apply_compose := by intro s; simp only [RenMap.rmap]; simp

mutual
@[simp]
def Value.smap (σ : SubstVec [Value, Ty]) : Value -> Value
| .var x => σ.1.act x
| .lam A t => .lam A[σ.2.1] (t.smap $ σ.lift [1, 0])
| .tlam t => .tlam (t.smap $ σ |> .lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)

@[simp]
def Term.smap (σ : SubstVec [Value, Ty]) : Term -> Term
| .val v => .val (v.smap σ)
| .app f a => .app (f.smap σ) (a.smap σ)
| .tapp f A => .tapp (f.smap σ) A[σ.2.1]
end

instance : SubstMap Value [Value, Ty] where
  smap := Value.smap

instance : SubstMap Term [Value, Ty] where
  smap := Term.smap

@[simp]
theorem Value.smap_fix {σ : SubstVec [Value, Ty]} {t : Value} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Term.smap_fix {σ : SubstVec [Value, Ty]} {t : Term} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[simp]
theorem Value.smap_term_ty_var {x} {σ : SubstVec [Value, Ty]} : (var x)[σ,] = σ.1.act x := rfl

@[simp]
theorem Term.smap_term_ty_app {t1 t2} {σ : SubstVec [Value, Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Value.smap_term_ty_lam {A t} {σ : SubstVec [Value, Ty]}
  : (lam A t)[σ,] = lam A[σ.2.1] t[σ.lift [1, 0],]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_tapp {t1 t2} {σ : SubstVec [Value, Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.2.1]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_term_ty_tlam {t} {σ : SubstVec [Value, Ty]} : (tlam t)[σ,] = tlam t[σ |> .lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_val {t1} {σ : SubstVec [Value, Ty]}
  : (val t1)[σ,] = val t1[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

instance : SubstSuffix Value [Ty] := ⟨⟩
instance : SubstMap Value [Ty] where
  smap r := Value.smap (Subst.id Value, r.1, .nil)

instance : SubstSuffix Term [Ty] := ⟨⟩
instance : SubstMap Term [Ty] where
  smap r := Term.smap (Subst.id Value, r.1, .nil)

@[simp]
theorem Value.smap_ty_var {x} {σ : SubstVec [Ty]} : (var x)[σ,] = var x := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_ty_app {t1 t2} {σ : SubstVec [Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_ty_lam {A t} {σ : SubstVec [Ty]}
  : (lam A t)[σ,] = lam A[σ.1] t[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_ty_tapp {t1 t2} {σ : SubstVec [Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.1]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_ty_tlam {t} {σ : SubstVec [Ty]} : (tlam t)[σ,] = tlam t[σ.lift [1],] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_ty_val {t1} {σ : SubstVec [Ty]}
  : (val t1)[σ,] = val t1[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

instance : SubstMap Value [Value] where
  smap r := Value.smap (r.1, Subst.id Ty, .nil)

instance : SubstMap Term [Value] where
  smap r := Term.smap (r.1, Subst.id Ty, .nil)

@[simp]
theorem Value.smap_term_var {x} {σ : SubstVec [Value]} : (var x)[σ,] = σ.1.act x := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_app {t1 t2} {σ : SubstVec [Value]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_term_lam {A t} {σ : SubstVec [Value]}
  : (lam A t)[σ,] = lam A t[σ.lift [1],]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_tapp {t1 t2} {σ : SubstVec [Value]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.smap_term_tlam {t} {σ : SubstVec [Value]} : (tlam t)[σ,] = tlam t[σ |> .ren Value [Ty] (𝐫1, .nil) 0 rfl,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_val {t1} {σ : SubstVec [Value]}
  : (val t1)[σ,] = val t1[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Value.from_action_smap {t : Action Value} {σ : SubstVec [Value, Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp [from_action]

@[simp]
theorem Value.from_action_smap0 {t : Action Value} {σ : SubstVec [Value]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp [from_action]

@[simp]
theorem Value.from_action_smap1 {t : Action Value} {σ : SubstVec [Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp [from_action]

instance : SubstSuffix Value [] := ⟨⟩
instance : SubstMap Value [] where
  smap _ := id

instance : SubstSuffix Term [] := ⟨⟩
instance : SubstMap Term [] where
  smap _ := id

@[reducible, simp]
instance instSubstMapAll_Value : SubstMapAll [Value] := .cons .nil

@[reducible, simp]
instance instSubstMapAll_Value_Ty : SubstMapAll [Value, Ty] := .cons instSubstMapAll_Ty

instance : SubstMapEmpty Value where
  apply_empty := by intro s; simp [SubstMap.smap]

instance : SubstMapEmpty Term where
  apply_empty := by intro s; simp [SubstMap.smap]

mutual
  @[grind =]
  theorem Value.ren_ren : ∀ {s : Value} {r1 : Ren Value} {r2 : RenVec [Ty]}, s⟨r1⟩⟨r2,⟩ = s⟨r2,⟩⟨r1⟩
  | .var x, r1, r2 => by simp
  | .lam A t, r1, r2 =>
    have ih := t.ren_ren (r1 := r1.lift) (r2 := r2)
    by simp [*]
  | .tlam t, r1, r2 =>
    have ih := t.ren_ren (r1 := r1) (r2 := r2.lift [1])
    by simp [*]

  @[grind =]
  theorem Term.ren_ren : ∀ {s : Term} {r1 : Ren Value} {r2 : RenVec [Ty]}, s⟨r1⟩⟨r2,⟩ = s⟨r2,⟩⟨r1⟩
  | .val v, r1, r2 =>
    have ih := v.ren_ren (r1 := r1) (r2 := r2)
    by simp [*]
  | .app f a, r1, r2 =>
    have ih1 := f.ren_ren (r1 := r1) (r2 := r2)
    have ih2 := a.ren_ren (r1 := r1) (r2 := r2)
    by simp [*]
  | .tapp f A, r1, r2 =>
    have ih1 := f.ren_ren (r1 := r1) (r2 := r2)
    by simp [*]
end

instance : SuffixCommuteRenRen Value [Ty] where
  ren_ren := Value.ren_ren

mutual
  theorem Value.ren_sub : ∀ {s : Value} {r : Ren Value} {τ : SubstVec [Ty]}, s⟨r⟩[τ,] = s[τ,]⟨r⟩
  | .var x, r, τ => by simp
  | .lam A t, r, τ =>
    have ih := t.ren_sub (r := r.lift) (τ := τ)
    by simp [*]
  | .tlam t, r, τ =>
    have ih := t.ren_sub (r := r) (τ := τ.lift [1])
    by simp [*]

  theorem Term.ren_sub : ∀ {s : Term} {r : Ren Value} {τ : SubstVec [Ty]}, s⟨r⟩[τ,] = s[τ,]⟨r⟩
  | .val v, r, τ =>
    have ih := v.ren_sub (r := r) (τ := τ)
    by simp [*]
  | .app f a, r, τ =>
    have ih1 := f.ren_sub (r := r) (τ := τ)
    have ih2 := a.ren_sub (r := r) (τ := τ)
    by simp [*]
  | .tapp f A, r, τ =>
    have ih1 := f.ren_sub (r := r) (τ := τ)
    by simp [*]
end

instance : SuffixCommuteRenSub Value [Ty] where
  ren_sub := Value.ren_sub

mutual
  theorem Value.smap_vecdef : ∀ {s : Value} {σ : SubstVec [Value, Ty]}, s[σ,] = s[σ.snd,][σ.fst]
  | .var x, σ => by simp
  | .lam A t, σ =>
    have ih := t.smap_vecdef (σ := σ.lift [1, 0])
    by simp [*]
  | .tlam t, σ =>
    have ih := t.smap_vecdef (σ := σ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by simp [*]

  theorem Term.smap_vecdef : ∀ {s : Term} {σ : SubstVec [Value, Ty]}, s[σ,] = s[σ.snd,][σ.fst]
  | .val v, σ =>
    have ih := v.smap_vecdef (σ := σ)
    by simp [*]
  | .app f a, σ =>
    have ih1 := f.smap_vecdef (σ := σ)
    have ih2 := a.smap_vecdef (σ := σ)
    by simp [*]
  | .tapp f A, σ =>
    have ih := f.smap_vecdef (σ := σ)
    by simp [*]
end

instance : SubstMapVecDef Value Value [Ty] where
  apply_vecdef := Value.smap_vecdef

instance : SubstMapVecDef Term Value [Ty] where
  apply_vecdef := Term.smap_vecdef

mutual
  @[simp]
  theorem Value.smap_id :  ∀ {s : Value}, s[SubstVec.id [Ty],] = s
  | .var x => by simp
  | .lam A t =>
    have ih := t.smap_id
    by simp [*]
  | .tlam t =>
    have ih := t.smap_id
    by simp [*]

  @[simp]
  theorem Term.smap_id :  ∀ {s : Term}, s[SubstVec.id [Ty],] = s
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
  apply_id := Value.smap_id

instance : SubstMapId Term [Value, Ty] where
  apply_id := Term.smap_id

instance : SubstMapId Value [Value] where
  apply_id := by intro s; simp only [SubstMap.smap]; simp

instance : SubstMapId Term [Value] where
  apply_id := by intro s; simp only [SubstMap.smap]; simp

instance : SubstMapId Value [Ty] where
  apply_id := by intro s; simp only [SubstMap.smap]; simp

instance : SubstMapId Term [Ty] where
  apply_id := by intro s; simp only [SubstMap.smap]; simp

mutual
  @[simp]
  theorem Value.smap_ren_compose_left_ty : ∀ {s : Value} {r : RenVec [Ty]} {τ : SubstVec [Ty]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .var x, r, τ => by simp
  | .lam A t, r, τ =>
    have ih1 := t.smap_ren_compose_left_ty (r := r) (τ := τ)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, τ =>
    have ih := t.smap_ren_compose_left_ty
      (r := r.lift [1])
      (τ := τ.lift [1])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_left_ty : ∀ {s : Term} {r : RenVec [Ty]} {τ : SubstVec [Ty]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .val v, r, τ =>
    have ih1 := v.smap_ren_compose_left_ty (r := r) (τ := τ)
    by simp [*]
  | .app f a, r, τ =>
    have ih1 := f.smap_ren_compose_left_ty (r := r) (τ := τ)
    have ih2 := a.smap_ren_compose_left_ty (r := r) (τ := τ)
    by simp [*]
  | .tapp f A, r, τ =>
    have ih1 := f.smap_ren_compose_left_ty (r := r) (τ := τ)
    by simp [*]
end

instance : SubstMapRenComposeLeft Value [Ty] where
  apply_ren_compose_left := Value.smap_ren_compose_left_ty

instance : SubstMapRenComposeLeft Term [Ty] where
  apply_ren_compose_left := Term.smap_ren_compose_left_ty

mutual
  @[simp]
  theorem Value.smap_ren_compose_right_ty : ∀ {s : Value} {r : RenVec [Ty]} {σ : SubstVec [Ty]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .var x, r, σ => by simp
  | .lam A t, r, σ =>
    have ih1 := t.smap_ren_compose_right_ty (r := r) (σ := σ)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, σ =>
    have ih := t.smap_ren_compose_right_ty
      (r := r.lift [1])
      (σ := σ.lift [1])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_right_ty : ∀ {s : Term} {r : RenVec [Ty]} {σ : SubstVec [Ty]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .val v, r, σ =>
    have ih1 := v.smap_ren_compose_right_ty (r := r) (σ := σ)
    by simp [*]
  | .app f a, r, σ =>
    have ih1 := f.smap_ren_compose_right_ty (r := r) (σ := σ)
    have ih2 := a.smap_ren_compose_right_ty (r := r) (σ := σ)
    by simp [*]
  | .tapp f A, r, σ =>
    have ih1 := f.smap_ren_compose_right_ty (r := r) (σ := σ)
    by simp [*]
end

instance : SubstMapRenComposeRight Value [Ty] where
  apply_ren_compose_right := Value.smap_ren_compose_right_ty

instance : SubstMapRenComposeRight Term [Ty] where
  apply_ren_compose_right := Term.smap_ren_compose_right_ty

mutual
  @[simp]
  theorem Value.smap_compose_ty : ∀ {s : Value} {σ τ : SubstVec [Ty]}, s[σ,][τ,] = s[σ >> τ,]
  | .var x, σ, τ => by simp
  | .lam A t, σ, τ =>
    have ih1 := t.smap_compose_ty (σ := σ) (τ := τ)
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      try simp [Subst.rewrite_lift_compose (T := Value), *]
      simp [*] at *; congr
    }
  | .tlam t, σ, τ =>
    have ih := t.smap_compose_ty (σ := σ.lift [1]) (τ := τ.lift [1])
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      try simp [Subst.rewrite_lift_compose (T := Value), *]
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_compose_ty : ∀ {s : Term} {σ τ : SubstVec [Ty]}, s[σ,][τ,] = s[σ >> τ,]
  | .val v, σ, τ =>
    have ih1 := v.smap_compose_ty (σ := σ) (τ := τ)
    by simp [*]
  | .app f a, σ, τ =>
    have ih1 := f.smap_compose_ty (σ := σ) (τ := τ)
    have ih2 := a.smap_compose_ty (σ := σ) (τ := τ)
    by simp [*]
  | .tapp f A, σ, τ =>
    have ih1 := f.smap_compose_ty (σ := σ) (τ := τ)
    by simp [*]
end

instance : SubstMapCompose Value [Ty] where
  apply_compose := Value.smap_compose_ty

instance : SubstMapCompose Term [Ty] where
  apply_compose := Term.smap_compose_ty

mutual
  @[simp]
  theorem Value.smap_ren_compose_left_value : ∀ {s : Value} {r : RenVec [Value]} {τ : SubstVec [Value]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .var x, r, τ => by simp
  | .lam A t, r, τ =>
    have ih1 := t.smap_ren_compose_left_value (r := r.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, τ =>
    have ih := t.smap_ren_compose_left_value
      (r := r.lift [0, 1])
      (τ := τ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_left_value : ∀ {s : Term} {r : RenVec [Value]} {τ : SubstVec [Value]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .val v, r, τ =>
    have ih1 := v.smap_ren_compose_left_value (r := r) (τ := τ)
    by simp [*]
  | .app f a, r, τ =>
    have ih1 := f.smap_ren_compose_left_value (r := r) (τ := τ)
    have ih2 := a.smap_ren_compose_left_value (r := r) (τ := τ)
    by simp [*]
  | .tapp f A, r, τ =>
    have ih1 := f.smap_ren_compose_left_value (r := r) (τ := τ)
    by simp [*]
end

instance : SubstMapRenComposeLeft Value [Value] where
  apply_ren_compose_left := Value.smap_ren_compose_left_value

instance : SubstMapRenComposeLeft Term [Value] where
  apply_ren_compose_left := Term.smap_ren_compose_left_value

mutual
  @[simp]
  theorem Value.smap_ren_compose_right_value : ∀ {s : Value} {r : RenVec [Value]} {σ : SubstVec [Value]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .var x, r, σ => by simp; grind
  | .lam A t, r, σ =>
    have ih1 := t.smap_ren_compose_right_value (r := r.lift [1, 0]) (σ := σ.lift [1, 0])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, σ =>
    have ih := t.smap_ren_compose_right_value
      (r := r.lift [0, 1])
      (σ := σ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_ren_compose_right_value : ∀ {s : Term} {r : RenVec [Value]} {σ : SubstVec [Value]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .val v, r, σ =>
    have ih1 := v.smap_ren_compose_right_value (r := r) (σ := σ)
    by simp [*]
  | .app f a, r, σ =>
    have ih1 := f.smap_ren_compose_right_value (r := r) (σ := σ)
    have ih2 := a.smap_ren_compose_right_value (r := r) (σ := σ)
    by simp [*]
  | .tapp f A, r, σ =>
    have ih1 := f.smap_ren_compose_right_value (r := r) (σ := σ)
    by simp [*]
end

instance : SubstMapRenComposeRight Value [Value] where
  apply_ren_compose_right := Value.smap_ren_compose_right_value

instance : SubstMapRenComposeRight Term [Value] where
  apply_ren_compose_right := Term.smap_ren_compose_right_value

mutual
  theorem Value.sub_ren : ∀ {s : Value} {σ : Subst Value} {r : RenVec [Ty]}, s[σ]⟨r,⟩ = s⟨r,⟩[σ⟨r,⟩]
  | .var x, σ, r => by simp
  | .lam A t, σ, r =>
    have ih := t.sub_ren (σ := σ.lift) (r := r)
    by simp [*]
  | .tlam t, σ, r =>
    have ih := t.sub_ren (σ := σ⟨𝐫1(Ty)⟩) (r := r.lift [1])
    by {
      simp; rw [ih]; congr 2; simp
      rcases r with ⟨r, _, _⟩; simp
      grind
    }

  theorem Term.sub_ren : ∀ {s : Term} {σ : Subst Value} {r : RenVec [Ty]}, s[σ]⟨r,⟩ = s⟨r,⟩[σ⟨r,⟩]
  | .val v, σ, r =>
    have ih := v.sub_ren (σ := σ) (r := r)
    by simp [*]
  | .app f a, σ, r =>
    have ih1 := f.sub_ren (σ := σ) (r := r)
    have ih2 := a.sub_ren (σ := σ) (r := r)
    by simp [*]
  | .tapp f A, σ, r =>
    have ih1 := f.sub_ren (σ := σ) (r := r)
    by simp [*]
end

instance : SuffixCommuteSubRen Value [Ty] where
  sub_ren := Value.sub_ren

mutual
  @[simp]
  theorem Value.smap_compose_value : ∀ {s : Value} {σ τ : SubstVec [Value]}, s[σ,][τ,] = s[σ >> τ,]
  | .var x, σ, τ => by simp; grind
  | .lam A t, σ, τ =>
    have ih1 := t.smap_compose_value (σ := σ.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      try simp [Subst.rewrite_lift_compose (T := Value), *]
      simp [*] at *; congr
    }
  | .tlam t, σ, τ =>
    have ih := t.smap_compose_value
      (σ := σ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
      (τ := τ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp at *; rw [ih]
    }

  @[simp]
  theorem Term.smap_compose_value : ∀ {s : Term} {σ τ : SubstVec [Value]}, s[σ,][τ,] = s[σ >> τ,]
  | .val v, σ, τ =>
    have ih1 := v.smap_compose_value (σ := σ) (τ := τ)
    by simp [*]
  | .app f a, σ, τ =>
    have ih1 := f.smap_compose_value (σ := σ) (τ := τ)
    have ih2 := a.smap_compose_value (σ := σ) (τ := τ)
    by simp [*]
  | .tapp f A, σ, τ =>
    have ih1 := f.smap_compose_value (σ := σ) (τ := τ)
    by simp [*]
end

instance : SubstMapCompose Value [Value] where
  apply_compose := Value.smap_compose_value

instance : SubstMapCompose Term [Value] where
  apply_compose := Term.smap_compose_value

mutual
  @[simp]
  theorem Value.smap_ren_compose_left : ∀ {s : Value} {r : RenVec [Value, Ty]} {τ : SubstVec [Value, Ty]}, s⟨r,⟩[τ,] = s[r >> τ,]
  | .var x, r, τ => by simp
  | .lam A t, r, τ =>
    have ih1 := t.smap_ren_compose_left (r := r.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, τ =>
    have ih := t.smap_ren_compose_left
      (r := r.lift [0, 1])
      (τ := τ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
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

instance : SubstMapRenComposeLeft Value [Value, Ty] where
  apply_ren_compose_left := Value.smap_ren_compose_left

instance : SubstMapRenComposeLeft Term [Value, Ty] where
  apply_ren_compose_left := Term.smap_ren_compose_left

mutual
  @[simp]
  theorem Value.smap_ren_compose_right : ∀ {s : Value} {r : RenVec [Value, Ty]} {σ : SubstVec [Value, Ty]}, s[σ,]⟨r,⟩ = s[σ >> r,]
  | .var x, r, σ => by simp; grind
  | .lam A t, r, σ =>
    have ih1 := t.smap_ren_compose_right (r := r.lift [1, 0]) (σ := σ.lift [1, 0])
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp [*] at *; congr
    }
  | .tlam t, r, σ =>
    have ih := t.smap_ren_compose_right
      (r := r.lift [0, 1])
      (σ := σ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases r with ⟨r1, r2, _, _⟩
      rcases σ with ⟨σ1, σ2, _, _⟩
      simp at *; rw [ih]; congr 1
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
    by simp [*]
end

instance : SubstMapRenComposeRight Value [Value, Ty] where
  apply_ren_compose_right := Value.smap_ren_compose_right

instance : SubstMapRenComposeRight Term [Value, Ty] where
  apply_ren_compose_right := Term.smap_ren_compose_right

mutual
  @[simp]
  theorem Value.smap_compose : ∀ {s : Value} {σ τ : SubstVec [Value, Ty]}, s[σ,][τ,] = s[σ >> τ,]
  | .var x, σ, τ => by simp; grind
  | .lam A t, σ, τ =>
    have ih1 := t.smap_compose (σ := σ.lift [1, 0]) (τ := τ.lift [1, 0])
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      try simp [Subst.rewrite_lift_compose (T := Value), *]
      simp [*] at *; congr
    }
  | .tlam t, σ, τ =>
    have ih := t.smap_compose
      (σ := σ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
      (τ := τ.lift [0, 1] |> .ren Value [Ty] (𝐫1, .nil) 0 rfl)
    by {
      rcases σ with ⟨σ1, σ2, _, _⟩
      rcases τ with ⟨τ1, τ2, _, _⟩
      try simp [Subst.rewrite_lift_compose (T := Value), *]
      simp at *; rw [ih]; congr 1
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
    by simp [*]
end

instance : SubstMapCompose Value [Value, Ty] where
  apply_compose := Value.smap_compose

instance : SubstMapCompose Term [Value, Ty] where
  apply_compose := Term.smap_compose

end SystemFCallByValue
