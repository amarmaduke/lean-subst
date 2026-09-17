
import LeanSubst
import LeanSubst.Automation.Basic

open LeanSubst

namespace SystemFWithNat

inductive Ty where
| var : Nat -> Ty
| arrow : Ty -> Ty -> Ty
| all : Ty -> Ty
| nat : Ty

-- #leansubst var Ty.var
-- #leansubst bind Ty at pos 0 in Ty.all
-- #leansubst generate Ty

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam (A : Ty) (t : Term) : Term
| tapp : Term -> Ty -> Term
| tlam (t : Term) : Term
| zero : Term
| succ : Term -> Term
| nrec (z : Term) (s : Term) (n : Term) : Term

-- #leansubst var Term.var
-- #leansubst bind Term at pos 1 in Term.lam
-- #leansubst bind Ty at pos 0 in Term.tlam
-- #leansubst bind 2 of Term at pos 1 in Term.nrec

-- #leansubst generate Term, Ty

-- -- Checking Ty --
-- #print Ty.from_action
-- #print Ty.from_action_id
-- #print Ty.from_action_succ
-- #print Ty.from_action_re
-- #print Ty.from_action_su

-- #check (inferInstance : Coe (Action Ty) Ty)

-- #print Ty.rmap
-- #print Ty.rmap._f

-- #check (inferInstance : RenMap Ty [Ty])

-- #print Ty.rmap_fix
-- #print Ty.rmap_empty -- should be removed

-- #check (inferInstance : RenSuffix Ty [])
-- #check (inferInstance : RenMap Ty [])
-- #check (inferInstance : RenMapAll [Ty])

-- #print Ty.rmap_var
-- #print Ty.rmap_arrow
-- #print Ty.rmap_all
-- #print Ty.rmap_nat
-- #print Ty.from_action_rmap

-- #check (inferInstance : RenMapEmpty Ty)
-- #check (inferInstance : RenMapId Ty [Ty])
-- #check (inferInstance : RenMapCompose Ty [Ty])

-- #print Ty.smap
-- #print Ty.smap._f

-- #check (inferInstance : SubstMap Ty [Ty])

-- #print Ty.smap_fix
-- #print Ty.smap_empty -- to be removed

-- #check (inferInstance : SubstSuffix Ty [])
-- #check (inferInstance : SubstMap Ty [])
-- #check (inferInstance : SubstMapAll [Ty])

-- #print Ty.smap_var
-- #print Ty.smap_arrow
-- #print Ty.smap_all
-- #print Ty.smap_nat
-- #print Ty.from_action_smap

-- #check (inferInstance : SubstMapEmpty Ty)
-- #check (inferInstance : SubstMapId Ty [Ty])
-- #check (inferInstance : SubstMapStable Ty [Ty])
-- #check (inferInstance : SubstMapRenComposeLeft Ty [Ty])
-- #check (inferInstance : SubstMapRenComposeRight Ty [Ty])
-- #check (inferInstance : SubstMapCompose Ty [Ty])

-- -- Checking Term --
-- #print Term.from_action
-- #print Term.from_action_id
-- #print Term.from_action_succ
-- #print Term.from_action_re
-- #print Term.from_action_su

-- #check (inferInstance : Coe (Action Term) Term)

-- -- rmap
-- #print Term.rmap
-- #print Term.rmap._f

-- #check (inferInstance : RenMap Term [Term, Ty])
-- #check (inferInstance : RenSuffix Term [Ty])
-- #check (inferInstance : RenMap Term [Ty])
-- #check (inferInstance : RenMap Term [Term])
-- #check (inferInstance : RenSuffix Term [])
-- #check (inferInstance : RenMap Term [])
-- #check (inferInstance : RenMapAll [Term])
-- #check (inferInstance : RenMapAll [Term, Ty])

-- #print Term.rmap_empty -- to be removed
-- #print Term.rmap_fix

-- #print Term.rmap_term_var
-- #print Term.rmap_term_app
-- #print Term.rmap_term_lam
-- #print Term.rmap_term_tapp
-- #print Term.rmap_term_tlam
-- #print Term.rmap_term_zero
-- #print Term.rmap_term_succ
-- #print Term.rmap_term_nrec

-- #print Term.rmap_ty_var
-- #print Term.rmap_ty_app
-- #print Term.rmap_ty_lam
-- #print Term.rmap_ty_tapp
-- #print Term.rmap_ty_tlam
-- #print Term.rmap_ty_zero
-- #print Term.rmap_ty_succ
-- #print Term.rmap_ty_nrec

-- #print Term.rmap_term_ty_var
-- #print Term.rmap_term_ty_app
-- #print Term.rmap_term_ty_lam
-- #print Term.rmap_term_ty_tapp
-- #print Term.rmap_term_ty_tlam
-- #print Term.rmap_term_ty_zero
-- #print Term.rmap_term_ty_succ
-- #print Term.rmap_term_ty_nrec

-- #print Term.from_action_rmap
-- #print Term.from_action_rmap0
-- #print Term.from_action_rmap1

-- #check (inferInstance : RenMapEmpty Term)
-- #check (inferInstance : RenMapVecDef Term Term [Ty])
-- #check (inferInstance : RenMapId Term [Term, Ty])
-- #check (inferInstance : RenMapCompose Term [Term, Ty])
-- #check (inferInstance : RenMapVecDef Term Term [])
-- #check (inferInstance : RenMapId Term [Term])
-- #check (inferInstance : RenMapCompose Term [Term])
-- #check (inferInstance : RenMapId Term [Ty])
-- #check (inferInstance : RenMapCompose Term [Ty])

-- -- smap
-- #print Term.smap
-- #print Term.smap._f

-- #check (inferInstance : SubstMap Term [Term, Ty])
-- #check (inferInstance : SubstSuffix Term [Ty])
-- #check (inferInstance : SubstMap Term [Ty])
-- #check (inferInstance : SubstMap Term [Term])
-- #check (inferInstance : SubstSuffix Term [])
-- #check (inferInstance : SubstMap Term [])
-- #check (inferInstance : SubstMapAll [Term])
-- #check (inferInstance : SubstMapAll [Term, Ty])

-- #print Term.smap_empty -- remove
-- #print Term.smap_fix

-- #print Term.smap_term_var
-- #print Term.smap_term_app
-- #print Term.smap_term_lam
-- #print Term.smap_term_tapp
-- #print Term.smap_term_tlam
-- #print Term.smap_term_zero
-- #print Term.smap_term_succ
-- #print Term.smap_term_nrec

-- #print Term.smap_ty_var
-- #print Term.smap_ty_app
-- #print Term.smap_ty_lam
-- #print Term.smap_ty_tapp
-- #print Term.smap_ty_tlam
-- #print Term.smap_ty_zero
-- #print Term.smap_ty_succ
-- #print Term.smap_ty_nrec

-- #print Term.smap_term_ty_var
-- #print Term.smap_term_ty_app
-- #print Term.smap_term_ty_lam
-- #print Term.smap_term_ty_tapp
-- #print Term.smap_term_ty_tlam
-- #print Term.smap_term_ty_zero
-- #print Term.smap_term_ty_succ
-- #print Term.smap_term_ty_nrec

-- #print Term.from_action_smap
-- #print Term.from_action_smap0
-- #print Term.from_action_smap1

-- #check (inferInstance : SuffixCommuteRenRen Term [Ty])
-- #check (inferInstance : SuffixCommuteRenSub Term [Ty])
-- #check (inferInstance : SuffixCommuteSubRen Term [Ty])
-- #check (inferInstance : SubstMapEmpty Term)

-- #check (inferInstance : SubstMapVecDef Term Term [Ty])
-- #check (inferInstance : SubstMapId Term [Term, Ty])
-- #check (inferInstance : SubstMapStable Term [Term, Ty])
-- #check (inferInstance : SubstMapRenComposeLeft Term [Term, Ty])
-- #check (inferInstance : SubstMapRenComposeRight Term [Term, Ty])

-- #check (inferInstance : SubstMapVecDef Term Term [])
-- #check (inferInstance : SubstMapId Term [Term])
-- #check (inferInstance : SubstMapStable Term [Term])
-- #check (inferInstance : SubstMapRenComposeLeft Term [Term])
-- #check (inferInstance : SubstMapRenComposeRight Term [Term])

-- #check (inferInstance : SubstMapId Term [Ty])
-- #check (inferInstance : SubstMapStable Term [Ty])
-- #check (inferInstance : SubstMapRenComposeLeft Term [Ty])
-- #check (inferInstance : SubstMapRenComposeRight Term [Ty])

-- #check (inferInstance : SubstMapCompose Term [Term, Ty])
-- #check (inferInstance : SubstMapCompose Term [Ty])
-- #check (inferInstance : SubstMapCompose Term [Term])

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
theorem Ty.from_action_re {n} : from_action (re n) = var n := by simp [from_action]

@[simp]
theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Ty) Ty where
  coe := Ty.from_action

@[simp]
def Ty.rmap (r : RenVec [Ty]) : Ty -> Ty
| var x => var (r.head.act x)
| nat => nat
| arrow t1 t2 => arrow (t1.rmap r) (t2.rmap r)
| all t => all $ t.rmap $ r.lift [1]

instance : RenMap Ty [Ty] where
  rmap := Ty.rmap

@[simp]
theorem Ty.rmap_fix {r : RenVec [Ty]} {t : Ty} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[reducible, simp]
instance instRenMapAll_Ty : RenMapAll [Ty] := .cons .nil

@[simp]
theorem Ty.rmap_var {x} {r : RenVec [Ty]} : (var x)⟨r,⟩ = .var (r.head.act x) := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Ty.rmap_nat {r : RenVec [Ty]} : (nat)⟨r,⟩ = nat := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Ty.rmap_arrow {t1 t2 : Ty} {r : RenVec [Ty]} : (arrow t1 t2)⟨r,⟩ = arrow t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Ty.rmap_all {t} {r : RenVec [Ty]} : (all t)⟨r,⟩ = all t⟨r.lift [1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Ty.from_action_rmap {t : Action Ty} {r : RenVec [Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp

instance : RenMapId Ty [Ty] where
  apply_id := by subst_solve_id

instance : RenMapCompose Ty [Ty] where
  apply_compose := by subst_solve_compose

@[simp]
def Ty.smap (σ : SubstVec [Ty]) : Ty -> Ty
| var x => σ.head.act x
| nat => nat
| arrow t1 t2 => arrow (t1.smap σ) (t2.smap σ)
| all t => all $ t.smap $ σ.lift [1]

instance : SubstMap Ty [Ty] where
  smap := Ty.smap

@[simp]
theorem Ty.smap_fix {σ : SubstVec [Ty]} {t : Ty} : smap σ t = t[σ,] := by simp [SubstMap.smap]

@[reducible, simp]
instance instSubstMapAll_Ty : SubstMapAll [Ty] := .cons .nil

@[simp]
theorem Ty.smap_var {x} {σ : SubstVec [Ty]} : (var x)[σ,] = σ.head.act x := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Ty.smap_nat {σ : SubstVec [Ty]} : (nat)[σ,] = nat := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Ty.smap_arrow {t1 t2 : Ty} {σ : SubstVec [Ty]} : (arrow t1 t2)[σ,] = arrow t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Ty.smap_all {t} {σ : SubstVec [Ty]} : (all t)[σ,] = all t[σ.lift [1],] := by
  simp only [SubstMap.smap]; rw [smap]

@[simp]
theorem Ty.from_action_smap {t : Action Ty} {σ : SubstVec [Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp

instance : SubstMapId Ty [Ty] where
  apply_id := by subst_solve_id

instance : SubstMapStable Ty [Ty] where
  apply_stable := by sorry --subst_solve_stable

instance : SubstMapRenComposeLeft Ty [Ty] where
  apply_ren_compose_left := by sorry --subst_solve_compose

instance : SubstMapRenComposeRight Ty [Ty] where
  apply_ren_compose_right := by sorry --subst_solve_compose

instance : SubstMapCompose Ty [Ty] where
  apply_compose := by subst_solve_compose

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
| var x => var (r.head.act x)
| app t1 t2 => app (t1.rmap r) (t2.rmap r)
| lam A t => lam A⟨r.tail.head⟩ (t.rmap $ r.lift [1, 0])
| tapp t A => tapp (t.rmap r) A⟨r.tail.head⟩
| tlam t => tlam (t.rmap $ r.lift [0, 1])
| zero => zero
| succ t => succ (t.rmap r)
| nrec z s n => nrec (z.rmap r) (s.rmap $ r.lift [2, 0]) (n.rmap r)

instance : RenMap Term [Term, Ty] where
  rmap := Term.rmap

@[simp]
theorem Term.rmap_fix {r : RenVec [Term, Ty]} {t : Term} : rmap r t = t⟨r,⟩ := by simp [RenMap.rmap]

@[simp]
theorem Term.rmap_term_ty_var {x} {r : RenVec [Term, Ty]} : (var x)⟨r,⟩ = var (r.head.act x) := rfl

@[simp]
theorem Term.rmap_term_ty_app {t1 t2} {r : RenVec [Term, Ty]} : (app t1 t2)⟨r,⟩ = app t1⟨r,⟩ t2⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]

@[simp]
theorem Term.rmap_term_ty_lam'' {A t} {r : RenVec [Term, Ty]}
  : (lam A t)⟨r,⟩ = lam A⟨r.tail.head⟩ t⟨r.lift [1, 0],⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_tapp {t1 t2} {r : RenVec [Term, Ty]}
  : (tapp t1 t2)⟨r,⟩ = tapp t1⟨r,⟩ t2⟨r.tail.head⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_tlam {t} {r : RenVec [Term, Ty]} : (tlam t)⟨r,⟩ = tlam t⟨r.lift [0, 1],⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_zero {r : RenVec [Term, Ty]} : zero⟨r,⟩ = zero := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_succ {t} {r : RenVec [Term, Ty]} : (succ t)⟨r,⟩ = succ t⟨r,⟩ := by
  simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.rmap_term_ty_nrec {z s n} {r : RenVec [Term, Ty]}
  : (nrec z s n)⟨r,⟩ = nrec z⟨r,⟩ s⟨r.lift [2, 0],⟩ n⟨r,⟩
:= by simp only [RenMap.rmap]; rw [rmap]; try simp

@[simp]
theorem Term.from_action_rmap {t : Action Term} {r : RenVec [Term, Ty]}
  : (from_action t)⟨r,⟩ = from_action t⟨r,⟩
:= by cases t <;> simp [from_action]

@[reducible, simp]
instance instRenMapAll_Term_Ty : RenMapAll [Term, Ty] := .cons instRenMapAll_Ty

instance : RenMapId Term [Term, Ty] where
  apply_id := by subst_solve_id

instance : RenMapCompose Term [Term, Ty] where
  apply_compose := by
    intro s r1 r2
    induction s generalizing r1 r2
    all_goals simp [*]; try rfl

@[simp]
def Term.smap (σ : SubstVec [Term, Ty]) : Term -> Term
| var x => σ.head.act x
| app t1 t2 => app (t1.smap σ) (t2.smap σ)
| lam A t => lam A[σ.tail.head] (t.smap $ σ.lift [1, 0])
| tapp t A => tapp (t.smap σ) A[σ.tail.head]
| tlam t => tlam (t.smap $ σ.lift [0, 1] >> ·⟨.add Term 1, .id Ty⟩)
| zero => zero
| succ t => succ (t.smap σ)
| nrec z s n => nrec (z.smap σ) (s.smap $ σ.lift [2, 0]) (n.smap σ)

instance : SubstMap Term [Term, Ty] where
  smap := Term.smap

@[simp]
theorem Term.smap_fix {σ : SubstVec [Term, Ty]} {t : Term} : smap σ t = t[σ,] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.smap_term_ty_var {x} {σ : SubstVec [Term, Ty]} : (var x)[σ,] = σ.head.act x := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_app {t1 t2} {σ : SubstVec [Term, Ty]} : (app t1 t2)[σ,] = app t1[σ,] t2[σ,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_lam {A t} {σ : SubstVec [Term, Ty]}
  : (lam A t)[σ,] = lam A[σ.tail.head] t[σ.lift [1, 0],]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_tapp {t1 t2} {σ : SubstVec [Term, Ty]}
  : (tapp t1 t2)[σ,] = tapp t1[σ,] t2[σ.tail.head]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_tlam {t} {σ : SubstVec [Term, Ty]}
  : (tlam t)[σ,] = tlam t[σ.lift [0, 1] >> ·⟨.add Term 1, .id Ty⟩,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_zero {σ : SubstVec [Term, Ty]} : zero[σ,] = zero := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_succ {t} {σ : SubstVec [Term, Ty]} : (succ t)[σ,] = succ t[σ,] := by
  simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.smap_term_ty_nrec {z s n} {σ : SubstVec [Term, Ty]}
  : (nrec z s n)[σ,] = nrec z[σ,] s[σ.lift [2, 0],] n[σ,]
:= by simp only [SubstMap.smap]; rw [smap]; try simp

@[simp]
theorem Term.from_action_smap {t : Action Term} {σ : SubstVec [Term, Ty]}
  : (from_action t)[σ,] = from_action t[σ,]
:= by cases t <;> simp [from_action]

@[reducible, simp]
instance instSubstMapAll_Term_Ty : SubstMapAll [Term, Ty] := .cons instSubstMapAll_Ty

instance : SubstMapId Term [Term, Ty] where
  apply_id := by
    intro s
    induction s
    all_goals simp [*]
    sorry --subst_solve_id

instance : SubstMapStable Term [Term, Ty] where
  apply_stable := by sorry --subst_solve_stable

instance : SubstMapRenComposeLeft Term [Term, Ty] where
  apply_ren_compose_left := by sorry --subst_solve_compose

instance : SubstMapRenComposeRight Term [Term, Ty] where
  apply_ren_compose_right := by sorry --subst_solve_compose

instance : SubstMapCompose Term [Term, Ty] where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    all_goals simp [*]
    case lam =>

      sorry
    case tapp => sorry
    case tlam =>
      cases σ; case _ σ1 σs =>
      cases σs; case _ σ2 σs =>
      cases σs
      cases τ; case _ τ1 τs =>
      cases τs; case _ τ2 τs =>
      cases τs
      simp
      sorry
    case nrec =>
      sorry

end SystemFWithNat
