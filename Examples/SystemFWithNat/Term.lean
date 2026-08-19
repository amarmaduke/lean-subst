
import LeanSubst
open LeanSubst

namespace SystemFWithNat

universe u2

@[simp]
theorem Subst.test {T n} : n :: Ren.add T (n + 1) = Ren.add T n := by
  induction n; simp
  simp [Ren.add, Ren.cons] at *
  funext; case _ i =>
  cases i <;> simp; omega

@[simp]
theorem Subst.test2 {T V} [RenMap T V] (r : RenVec V) : (Subst.id T)⟨r,⟩ = Subst.id T := by
  simp [RenMap.rmap, Subst.rmap, Subst.id]

inductive Ty where
| var : Nat -> Ty
| arrow : Ty -> Ty -> Ty
| all : Ty -> Ty
| nat : Ty

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam (A : Ty) (t : Term) : Term -- binds Term in t
| tapp : Term -> Ty -> Term
| tlam (t : Term) : Term -- binds Ty in t (does it make sense to allow a user to give a name instead of a position?)
| zero : Term
| succ : Term -> Term
| nrec (motive : Ty) (z : Term) (s : Term) (n : Term) : Term -- binds 2 Term's in s

----------------------------------------------------------------------------------------------------
-- Ty Renaming & Substitution
----------------------------------------------------------------------------------------------------
@[coe]
def Ty.from_action : Action Ty -> Ty
| re y => var y
| su t => t

@[simp]
theorem Ty.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp]
theorem Ty.from_action_succ {n} : from_action (𝐬1.act n) = var (n + 1) := by
  simp [from_action]

@[simp]
theorem Ty.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (r : RenVec [Ty]) : Ty -> Ty
| var x => var (r.1.act x)
| nat => nat
| arrow t1 t2 => arrow (t1.rmap r) (t2.rmap r)
| all t => all $ t.rmap $ r.lift [1]

instance : RenMap Ty [Ty] where
  rmap := Ty.rmap

@[reducible, simp]
instance instRenMapAll_Ty : RenMapAll [Ty] := .cons .nil

@[simp]
theorem Ty.rmap_var {x} {r : RenVec [Ty]} : (var x)⟨r,⟩ = .var (r.1.act x) := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.rmap_nat {r : RenVec [Ty]} : (nat)⟨r,⟩ = nat := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.rmap_app {t1 t2 : Ty} {r : RenVec [Ty]} : (arrow t1 t2)⟨r,⟩ = arrow t1⟨r,⟩ t2⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.rmap_all {t} {r : RenVec [Ty]} : (all t)⟨r,⟩ = all t⟨r.lift [1],⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Ty.from_action_rmap {t : Action Ty} {r : RenVec [Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by
  rcases r with ⟨r, u⟩
  cases u; case _ =>
  cases t <;> simp [Ty.from_action]

@[simp, grind =]
theorem Ty.apply_id : ∀ {s : Ty}, rmap (.id [Ty]) s = s := by subst_solve_id

instance : RenMapEmpty Ty where
  apply_empty := by intro s; simp

instance : RenMapId Ty [Ty] where
  apply_id := by intro s; simp [RenMap.rmap]; grind

instance : RenMapCompose Ty [Ty] where
  apply_compose := by subst_solve_compose

@[simp]
def Ty.smap (σ : SubstVec [Ty]) : Ty -> Ty
| var x => σ.1.act x
| nat => nat
| arrow t1 t2 => arrow (t1.smap σ) (t2.smap σ)
| all t => all $ t.smap $ σ.lift [1]

instance : SubstMap Ty [Ty] where
  smap := Ty.smap

instance instSubstMapAll_Ty : SubstMapAll [Ty] := .cons .nil

@[simp]
theorem Ty.smap_var {x} {σ : SubstVec [Ty]} : (var x)[σ,] = σ.1.act x := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.smap_nat {σ : SubstVec [Ty]} : (nat)[σ,] = nat := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.smap_app {t1 t2 : Ty} {σ : SubstVec [Ty]} : (arrow t1 t2)[σ,] = arrow t1[σ,] t2[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.smap_all {t} {σ : SubstVec [Ty]} : (all t)[σ,] = all t[σ.lift [1],] := by
  simp [SubstMap.smap]

@[simp]
theorem Ty.from_action_smap {t : Action Ty} {σ : SubstVec [Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by
  rcases σ with ⟨σ, u⟩
  cases u; case _ =>
  cases t <;> simp [Ty.from_action]

instance : SubstMapEmpty Ty where
  apply_empty := by intro s; simp

instance : SubstMapId Ty [Ty] where
  apply_id := by subst_solve_id

instance : SubstMapStable Ty [Ty] where
  apply_stable := by sorry

instance : SubstMapRenComposeLeft Ty [Ty] where
  apply_ren_compose_left := by sorry

instance : SubstMapRenComposeRight Ty [Ty] where
  apply_ren_compose_right := by sorry

instance : SubstMapCompose Ty [Ty] where
  apply_compose := by
    intro s σ τ
    let T := Subst.typeof s
    induction s generalizing σ τ
    all_goals
      try solve | simp; grind
      try solve | simp [*]
      try simp [Subst.lift_compose_ren_right_vec (T := T), *]
      try simp [Subst.rewrite_lift_compose_ren_left_vec (T := T), *]
      try simp [Subst.rewrite_lift_compose_vec (T := T), *]
    case var =>

      rcases σ with ⟨σ, u1⟩
      rcases τ with ⟨τ, u2⟩
      cases u1; cases u2; case _ =>
      simp
----------------------------------------------------------------------------------------------------
-- Term Renaming & Substitution
----------------------------------------------------------------------------------------------------

@[coe]
def Term.from_action : Action Term -> Term
| re y => var y
| su t => t

@[simp, grind =]
theorem Term.from_action_id {n} : from_action (𝐬0.act n) = var n := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_action_succ {n} : from_action (𝐬1.act n) = var (n + 1) := by
  simp [from_action]

@[simp, grind =]
theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp, grind =]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : RenVec [Term, Ty]) : Term -> Term
| var x => var ((r.get Term 0).act x)
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| lam A t => lam A⟨r.get Ty 1⟩ (t.rmap $ r.lift [1, 0])
| tapp t A => tapp (t.rmap r) A⟨r.get Ty 1⟩
| tlam t => tlam (t.rmap $ r.lift [0, 1])
| zero => zero
| succ t => succ (t.rmap r)
| nrec motive z s n => nrec motive⟨r.get Ty 1⟩ (z.rmap r) (s.rmap $ r.lift [2, 0]) (n.rmap r)

instance : RenMap Term [Term, Ty] where
  rmap := Term.rmap

@[simp]
theorem Term.rmap_term_ty_var {x} {r : RenVec [Term, Ty]} : (var x)⟨r,⟩ = var ((r.get Term 0).act x) := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_app {t1 t2} {r : RenVec [Term, Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_lam {A t} {r : RenVec [Term, Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.get Ty 1⟩ t⟨r.lift [1, 0],⟩
:= by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_tapp {t1 t2} {r : RenVec [Term, Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.get Ty 1⟩
:= by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_tlam {t} {r : RenVec [Term, Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [0, 1],⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_zero {r : RenVec [Term, Ty]} : zero⟨r,⟩ = zero := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_succ {t} {r : RenVec [Term, Ty]} : (succ t)⟨r,⟩ = succ t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_nrec {m z s n} {r : RenVec [Term, Ty]}
  : (nrec m z s n)⟨r,⟩ = nrec m⟨r.get Ty 1⟩ z⟨r,⟩ s⟨r.lift [2, 0],⟩ n⟨r,⟩
:= by simp [RenMap.rmap]

instance : RenMap Term [Ty] where
  rmap r := Term.rmap (Ren.id Term, r.1, .unit)

@[simp]
theorem Term.rmap_ty_var {x} {r : RenVec [Ty]} : (var x)⟨r,⟩ = var x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_ty_app {t1 t2} {r : RenVec [Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_ty_lam {A t} {r : RenVec [Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.get Ty 0⟩ t⟨r,⟩
:= by simp [RenMap.rmap]; try grind

@[simp]
theorem Term.rmap_ty_tapp {t1 t2} {r : RenVec [Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.get Ty 0⟩
:= by simp [RenMap.rmap]; try grind

@[simp]
theorem Term.rmap_ty_tlam {t} {r : RenVec [Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [1],⟩ := by
  simp +instances [RenMap.rmap]
  rcases r with ⟨r, u⟩; cases u -- TODO(FIX)
  simp

@[simp]
theorem Term.rmap_ty_zero {r : RenVec [Ty]} : zero⟨r,⟩ = zero := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_ty_succ {t} {r : RenVec [Ty]} : (succ t)⟨r,⟩ = succ t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_ty_nrec {m z s n} {r : RenVec [Ty]}
  : (nrec m z s n)⟨r,⟩ = nrec m⟨r.get Ty 0⟩ z⟨r,⟩ s⟨r,⟩ n⟨r,⟩
:= by simp [RenMap.rmap]; grind

instance : RenMap Term [Term] where
  rmap r := Term.rmap (r.1, Ren.id Ty, .unit)

@[simp]
theorem Term.rmap_term_var {x} {r : RenVec [Term]} : (var x)⟨r,⟩ = var ((r.get Term 0).act x) := by
  simp [RenMap.rmap]
  rcases r with ⟨r, u⟩; cases u -- TODO(FIX)
  simp

@[simp]
theorem Term.rmap_term_app {t1 t2} {r : RenVec [Term]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_lam {A t} {r : RenVec [Term]}
  : (lam A t)⟨r,⟩ = lam A t⟨r.lift [1],⟩
:= by sorry

@[simp]
theorem Term.rmap_term_tapp {t1 t2} {r : RenVec [Term]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2
:= by simp [RenMap.rmap]; grind

@[simp]
theorem Term.rmap_term_tlam {t} {r : RenVec [Term]} : (tlam t)⟨r,⟩ = tlam t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_zero {r : RenVec [Term]} : zero⟨r,⟩ = zero := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_succ {t} {r : RenVec [Term]} : (succ t)⟨r,⟩ = succ t⟨r,⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_nrec {m z s n} {r : RenVec [Term]}
  : (nrec m z s n)⟨r,⟩ = nrec m z⟨r,⟩ s⟨r.lift [2],⟩ n⟨r,⟩
:= by simp [RenMap.rmap]; sorry

@[reducible, simp]
instance instRenMapAll_Term : RenMapAll [Term] := .cons .nil

@[reducible, simp]
instance instRenMapAll_Term_Ty : RenMapAll [Term, Ty] := .cons instRenMapAll_Ty

-- @[simp]
-- theorem Term.from_action_rmap {t : Action Term} {r : RenVec [Term, Ty]}
--   : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
-- := by
--   rcases r with ⟨r1, r2, u⟩
--   cases u; case _ =>
--   cases t <;> simp [Term.from_action, RenVec.get]

instance : RenMapId Term [Term, Ty] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term, Ty] where
  apply_compose := by sorry

instance : RenMapId Term [Term] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term] where
  apply_compose := by sorry

instance : RenMapId Term [Ty] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Ty] where
  apply_compose := by sorry

@[simp]
def Term.smap (σ : SubstVec [Term, Ty]) : Term -> Term
| var x => (σ.get Term 0).act x
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| lam A t => lam A[σ.get Ty 1] (t.smap $ σ.lift [1, 0])
| tapp t A => tapp (t.smap σ) A[σ.get Ty 1]
| tlam t => tlam (t.smap $ σ.map 𝐭[(·⟨𝐫1(Ty)⟩), .lift])
| zero => zero
| succ t => succ (t.smap σ)
| nrec motive z s n =>
  nrec motive[σ.get Ty 1] (z.smap σ) (s.smap $ σ.lift [2, 0]) (n.smap σ)

instance : SubstMap Term [Term, Ty] where
  smap := Term.smap

@[simp]
theorem Term.smap_term_ty_var {x} {σ : SubstVec [Term, Ty]} : (var x)[σ,] = (σ.get Term 0).act x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_app {t1 t2} {σ : SubstVec [Term, Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_lam {A t} {σ : SubstVec [Term, Ty]}
  : (lam A t)[σ,] = lam A[σ.get Ty 1] t[σ.lift [1, 0],]
:= by simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_tapp {t1 t2} {σ : SubstVec [Term, Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.get Ty 1]
:= by simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_tlam {t} {σ : SubstVec [Term, Ty]}
  : (tlam t)[σ,] = tlam t[σ.map 𝐭[λ (τ : Subst Term) => τ⟨Ren.add Ty 1⟩, .lift],]
:= by simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_zero {σ : SubstVec [Term, Ty]} : zero[σ,] = zero := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_succ {t} {σ : SubstVec [Term, Ty]} : (succ t)[σ,] = succ t[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_nrec {m z s n} {σ : SubstVec [Term, Ty]}
  : (nrec m z s n)[σ,] = nrec m[σ.get Ty 1] z[σ,] s[σ.lift [2, 0],] n[σ,]
:= by simp [SubstMap.smap]

@[simp]
instance : SubstMap Term [Term] where
  smap σ := Term.smap (σ.get Term 0, Subst.id Ty, .unit)

@[simp]
theorem Term.smap_term_var {x} {σ : SubstVec [Term]} : (var x)[σ,] = (σ.get Term 0).act x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_app {t1 t2} {σ : SubstVec [Term]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_lam {A t} {σ : SubstVec [Term]}
  : (lam A t)[σ,] = lam A t[σ.lift [1],]
:= by simp [SubstMap.smap]; sorry


@[simp]
theorem Term.smap_term_tapp {t1 t2} {σ : SubstVec [Term]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2
:= by simp [SubstMap.smap]; sorry

@[simp]
theorem Term.smap_term_tlam {t} {σ : SubstVec [Term]}
  : (tlam t)[σ,] = tlam t[σ.map 𝐭[λ (τ : Subst Term) => τ⟨Ren.add Ty 1⟩],]
:= by simp [SubstMap.smap]; sorry

@[simp]
theorem Term.smap_term_zero {σ : SubstVec [Term]} : zero[σ,] = zero := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_succ {t} {σ : SubstVec [Term]} : (succ t)[σ,] = succ t[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_nrec {m z s n} {σ : SubstVec [Term]}
  : (nrec m z s n)[σ,] = nrec m z[σ,] s[σ.lift [2],] n[σ,]
:= by simp [SubstMap.smap]; sorry

@[simp]
instance : SubstMap Term [Ty] where
  smap σ := Term.smap (Subst.id Term, σ.get Ty 0, .unit)

@[simp]
theorem Term.smap_ty_var {x} {σ : SubstVec [Ty]} : (var x)[σ,] = var x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_app {t1 t2} {σ : SubstVec [Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_lam {A t} {σ : SubstVec [Ty]}
  : (lam A t)[σ,] = lam A[σ.get Ty 0] t[σ,]
:= by simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_tapp {t1 t2} {σ : SubstVec [Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.get Ty 0]
:= by simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_tlam {t} {σ : SubstVec [Ty]}
  : (tlam t)[σ,] = tlam t[σ.map 𝐭[.lift],]
:= by simp [SubstMap.smap]; sorry

@[simp]
theorem Term.smap_ty_zero {σ : SubstVec [Ty]} : zero[σ,] = zero := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_succ {t} {σ : SubstVec [Ty]} : (succ t)[σ,] = succ t[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_ty_nrec {m z s n} {σ : SubstVec [Ty]}
  : (nrec m z s n)[σ,] = nrec m[σ.get Ty 0] z[σ,] s[σ,] n[σ,]
:= by simp [SubstMap.smap]

@[reducible, simp]
instance instSubstMapAll_Term : SubstMapAll [Term] := .cons .nil

@[reducible, simp]
instance instSubstMapAll_Term_Ty : SubstMapAll [Term, Ty] := .cons instSubstMapAll_Ty

@[simp]
theorem Term.from_action_smap {t : Action Term} {σ : SubstVec [Term]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by
  sorry

instance : SubstMapId Term [Term, Ty] where
  apply_id := by subst_solve_id

instance : SubstMapStable Term [Term, Ty] where
  apply_stable := by sorry

@[simp]
theorem Term.apply_ren_compose_left {s : Term} {r : RenVec [Term, Ty]} {τ : SubstVec [Term, Ty]}
  : smap τ (rmap r s) = smap (r >> τ) s
:= by
  sorry

instance : SubstMapRenComposeLeft Term [Term, Ty] where
  apply_ren_compose_left := by intro s σ τ; simp [SubstMap.smap, RenMap.rmap]; try rfl

instance : SubstMapRenComposeRight Term [Term, Ty] where
  apply_ren_compose_right := by sorry

@[grind =]
theorem Term.smap_composition_lemma {s : Term} {σ : Subst Term} {τ : Subst Ty} :
  s[σ, τ] = s[τ][σ]
:= by
  induction s generalizing σ τ
  all_goals try solve | simp [*]

@[simp]
theorem Term.apply_compose
  : ∀ s σ τ, smap τ (smap σ s) = smap (σ >> τ) s
:= by
  intro s σ τ
  let T := Subst.typeof s
  induction s generalizing σ τ
  all_goals
    try solve | simp; grind
    try solve | simp [*]
    try simp [Subst.lift_compose_ren_right_vec (T := T), *]
    try simp [Subst.rewrite_lift_compose_ren_left_vec (T := T), *]
    try simp [Subst.rewrite_lift_compose_vec (T := T), *]
    try simp [Subst.compose_ren_left_vec_map_commute (T := T), *]
    try rfl
  case lam => sorry
  case nrec => sorry
  case tapp => sorry
  case var =>
    sorry
    -- rcases σ with ⟨σ1, σ2, u1⟩
    -- rcases τ with ⟨τ1, τ2, u2⟩
    -- cases u1; cases u2; case _ x =>
    -- simp
    -- simp; generalize zdef : σ1.act x = z
    -- cases z <;> simp
    -- case re y =>
    --   unfold SubstMap.smap
    --   unfold instSubstMapActionConsNil; simp
    --   unfold instSubstMapSubst; simp
    --   unfold Subst.smap; simp
    --   rw [zdef]; unfold LeanSubst.smap
    --   unfold instSubstMapAction; simp

      -- unfold SubstMap.smap
      -- unfold instSubstMapActionConsNil; simp
      -- unfold instSubstMapSubst; simp
      -- unfold Subst.smap; simp
      -- rw [zdef]; unfold LeanSubst.smap
      -- unfold instSubstMapAction; simp
      -- unfold instSubstMapAllConsTermTyNil
      -- unfold SubstMapAll.get; simp
      -- unfold instSubstMap_Term_Term; simp
      -- have lem := Term.smap_composition_lemma (s := t) (σ := τ1) (τ := τ2)
      -- unfold LeanSubst.smap at lem
      -- unfold instSubstMapTermConsTyNil at lem
      -- unfold instSubstMap_Term_Term at lem; simp at lem
      -- rw [lem]
      -- unfold instSubstMap_Term_Ty; simp
      -- congr

instance : SubstMapCompose Term [Term, Ty] where
  apply_compose := by intro s σ τ; simp [SubstMap.smap]; try rfl

instance : SubstMapId Term [Term] where
  apply_id := by sorry

instance : SubstMapStable Term [Term] where
  apply_stable := by sorry

instance : SubstMapRenComposeLeft Term [Term] where
  apply_ren_compose_left := by sorry

instance : SubstMapRenComposeRight Term [Term] where
  apply_ren_compose_right := by sorry

instance : SubstMapCompose Term [Term] where
  apply_compose := by sorry

instance : SubstMapId Term [Ty] where
  apply_id := by sorry

instance : SubstMapStable Term [Ty] where
  apply_stable := by sorry

instance : SubstMapRenComposeLeft Term [Ty] where
  apply_ren_compose_left := by sorry

instance : SubstMapRenComposeRight Term [Ty] where
  apply_ren_compose_right := by sorry

instance : SubstMapCompose Term [Ty] where
  apply_compose := by sorry

end SystemFWithNat
