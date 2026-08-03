import LeanSubst
open LeanSubst

namespace Examples.SystemF2

--   inductive Ty where
--   | var : Nat -> Ty
--   | arr : Ty -> Ty -> Ty
--   | all : Ty -> Ty

--   prefix:max "t#" => Ty.var
--   infixr:85 "-:>" => Ty.arr
--   notation ":∀" t => Ty.all t

--   inductive Term where
--   | var : Nat -> Term
--   | app : Term -> Term -> Term
--   | lam : Ty -> Term -> Term
--   | tapp : Term -> Ty -> Term
--   | tlam : Term -> Term

--   prefix:max "#" => Term.var
--   infixl:65 "•" => Term.app
--   notation:100 "λ[" A "]" t => Term.lam A t
--   notation:65 f "•[" a "]" => Term.tapp f a
--   notation:100 "Λ" t => Term.tlam t

-- ----------------------------------------------------------------------------------------------------
-- ---- Ty setup
-- ----------------------------------------------------------------------------------------------------
--   @[coe]
--   def Ty.from_action : Action Ty -> Ty
--   | re y => t#y
--   | su t => t

--    @[simp, grind =]
--   theorem Ty.from_action_id {n} : from_action (+0σ.act n) = var n := by
--     simp [from_action]

--   @[simp, grind =]
--   theorem Ty.from_action_succ {n} : from_action (+1σ.act n) = var (n + 1) := by
--     simp [from_action]

--   @[simp, grind =]
--   theorem Ty.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

--   @[simp, grind =]
--   theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

--   instance : Coe (Action Ty) Ty where
--     coe := Ty.from_action

--   @[simp]
--   def Ty.rmap (r : Ren Ty) : Ty -> Ty
--   | t#x => t#(r.act x)
--   | t1 -:> t2 => rmap r t1 -:> rmap r t2
--   | :∀ t => :∀ rmap r.lift t

--   instance : RenMap Ty Ty where
--     rmap := Ty.rmap

--   @[simp, grind =]
--   theorem Ty.ren_var {x} {r : Ren Ty} : (Ty.var x)⟨r⟩ = .var (r.act x) := by
--     simp [RenMap.rmap]

--   @[simp, grind =]
--   theorem Ty.ren_arr {t1 t2} {r : Ren Ty} : (t1 -:> t2)⟨r⟩ = t1⟨r⟩ -:> t2⟨r⟩ := by
--     simp [RenMap.rmap]

--   @[simp, grind =]
--   theorem Ty.ren_all {t} {r : Ren Ty} : (:∀ t)⟨r⟩ = :∀ t⟨r.lift⟩ := by
--     simp [RenMap.rmap]

--   instance : RenMapId Ty Ty where
--     apply_id := by subst_solve_id

--   instance : RenMapCompose Ty Ty where
--     apply_compose := by subst_solve_compose

--   @[simp]
--   def Ty.smap (σ : Subst Ty) : Ty -> Ty
--   | t#x => σ.act x
--   | t1 -:> t2 => smap σ t1 -:> smap σ t2
--   | :∀ t => :∀ smap σ.lift t

--   instance : SubstMap Ty Ty where
--     smap := Ty.smap

--   @[simp, grind =]
--   theorem Ty.subst_var {x} {σ : Subst Ty} : (Ty.var x)[σ] = σ.act x := by
--     simp [SubstMap.smap]

--   @[simp, grind =]
--   theorem Ty.subst_arr {t1 t2} {σ : Subst Ty} : (t1 -:> t2)[σ] = t1[σ] -:> t2[σ] := by
--     simp [SubstMap.smap]

--   @[simp, grind =]
--   theorem Ty.subst_all {t} {σ : Subst Ty} : (:∀ t)[σ] = :∀ t[σ.lift] := by
--     simp [SubstMap.smap]

--   @[simp]
--   theorem Ty.from_action_compose {x : Nat} {σ τ : Subst Ty}
--     : (from_action (Subst.act σ x))[τ] = from_action ((σ ∘ τ).act x)
--   := by
--     simp [from_action, Subst.compose]
--     generalize zdef : σ.act x = z
--     cases z <;> simp [from_action]

--   @[simp]
--   theorem Ty.from_action_compose_ren {x : Nat} {σ : Subst Ty} {r : Ren Ty}
--     : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
--   := by
--     simp [Ty.from_action]
--     generalize zdef : σ.act x = z
--     cases z <;> simp

--   instance : SubstMapId Ty Ty where
--     apply_id := by subst_solve_id

--   instance : SubstMapStable Ty Ty where
--     apply_stable := by subst_solve_stable

--   instance : SubstMapRenComposeLeft Ty Ty where
--     apply_ren_compose_left := by subst_solve_compose

--   instance : SubstMapRenComposeRight Ty Ty where
--     apply_ren_compose_right := by subst_solve_compose

--   instance : SubstMapCompose Ty Ty where
--     apply_compose := by subst_solve_compose

-- ----------------------------------------------------------------------------------------------------
-- ---- Term setup
-- ----------------------------------------------------------------------------------------------------
--   @[coe]
--   def Term.from_action : Action Term -> Term
--   | re y => #y
--   | su t => t

--   @[simp, grind =]
--   theorem Term.from_action_id {n} : from_action (+0σ.act n) = var n := by
--     simp [from_action]

--   @[simp, grind =]
--   theorem Term.from_action_succ {n} : from_action (+1σ.act n) = var (n + 1) := by
--     simp [from_action]

--   @[simp, grind =]
--   theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

--   @[simp, grind =]
--   theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

--   instance : Coe (Action Term) Term where
--     coe := Term.from_action

--   @[simp]
--   def Term.rmap (r : Ren Term) (rt : Ren Ty) : Term -> Term
--   | #x => var (r.act x)
--   | app t1 t2 => (rmap r rt t1) • (rmap r rt t2)
--   | λ[A] t => λ[A⟨rt⟩] rmap r.lift rt t
--   | t1 •[A] => rmap r rt t1 •[A⟨rt⟩]
--   | Λ t => Λ rmap r rt.lift t

--   instance : RenVecMap Term #(Ty) where
--     rvmap := Term.rmap

--   instance : RenMap Term Ty where
--     rmap := Term.rmap (.id Term)

--   @[simp]
--   def Term.smap (σ : Subst Term) (σt : Subst Ty) : Term -> Term
--   | #x => σ.act x
--   | app t1 t2 => (smap σ σt t1) • (smap σ σt t2)
--   | λ[A] t => λ[A[σt]] smap σ.lift σt t
--   | t1 •[A] => smap σ σt t1 •[A[σt]]
--   | Λ t => Λ smap (σ ◾ Ren.succ Ty) σt.lift t

--   instance : SubstVecMap Term #(Ty) where
--     svmap := Term.smap

end Examples.SystemF2
