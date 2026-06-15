import LeanSubst
open LeanSubst

namespace Examples.SystemF

  inductive Ty where
  | var : Nat -> Ty
  | arr : Ty -> Ty -> Ty
  | all : Ty -> Ty

  prefix:max "t#" => Ty.var
  infixr:85 "-:>" => Ty.arr
  notation ":∀" t => Ty.all t

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Ty -> Term -> Term
  | tapp : Term -> Ty -> Term
  | tlam : Term -> Term

  prefix:max "#" => Term.var
  infixl:65 "•" => Term.app
  notation:100 "λ[" A "]" t => Term.lam A t
  notation:65 f "•[" a "]" => Term.tapp f a
  notation:100 "Λ" t => Term.tlam t

----------------------------------------------------------------------------------------------------
---- Ty setup
----------------------------------------------------------------------------------------------------
  @[coe]
  def Ty.from_action : Action Ty -> Ty
  | re y => t#y
  | su t => t

   @[simp, grind =]
  theorem Ty.from_action_id {n} : from_action (+0σ.act n) = var n := by
    simp [from_action]

  @[simp, grind =]
  theorem Ty.from_action_succ {n} : from_action (+1σ.act n) = var (n + 1) := by
    simp [from_action]

  @[simp, grind =]
  theorem Ty.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

  @[simp, grind =]
  theorem Ty.from_action_su {t} : from_action (su t) = t := by simp [from_action]

  instance : Coe (Action Ty) Ty where
    coe := Ty.from_action

  @[simp]
  def Ty.rmap (r : Ren Ty) : Ty -> Ty
  | t#x => t#(r.act x)
  | t1 -:> t2 => rmap r t1 -:> rmap r t2
  | :∀ t => :∀ rmap r.lift t

  instance : RenMap Ty Ty where
    rmap := Ty.rmap

  @[simp, grind =]
  theorem Ty.ren_var {x} {r : Ren Ty} : (Ty.var x)⟨r⟩ = .var (r.act x) := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Ty.ren_arr {t1 t2} {r : Ren Ty} : (t1 -:> t2)⟨r⟩ = t1⟨r⟩ -:> t2⟨r⟩ := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Ty.ren_all {t} {r : Ren Ty} : (:∀ t)⟨r⟩ = :∀ t⟨r.lift⟩ := by
    simp [RenMap.rmap]

  instance : RenMapId Ty Ty where
    apply_id := by subst_solve_id

  instance : RenMapCompose Ty Ty where
    apply_compose := by subst_solve_compose

  @[simp]
  def Ty.smap (σ : Subst Ty) : Ty -> Ty
  | t#x => σ.act x
  | t1 -:> t2 => smap σ t1 -:> smap σ t2
  | :∀ t => :∀ smap σ.lift t

  instance : SubstMap Ty Ty where
    smap := Ty.smap

  @[simp, grind =]
  theorem Ty.subst_var {x} {σ : Subst Ty} : (Ty.var x)[σ] = σ.act x := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Ty.subst_arr {t1 t2} {σ : Subst Ty} : (t1 -:> t2)[σ] = t1[σ] -:> t2[σ] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Ty.subst_all {t} {σ : Subst Ty} : (:∀ t)[σ] = :∀ t[σ.lift] := by
    simp [SubstMap.smap]

  @[simp]
  theorem Ty.from_action_compose {x : Nat} {σ τ : Subst Ty}
    : (from_action (Subst.act σ x))[τ] = from_action ((σ ∘ τ).act x)
  := by
    simp [from_action, Subst.compose]
    generalize zdef : σ.act x = z
    cases z <;> simp [from_action]

  @[simp]
  theorem Ty.from_action_compose_ren {x : Nat} {σ : Subst Ty} {r : Ren Ty}
    : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
  := by
    simp [Ty.from_action]
    generalize zdef : σ.act x = z
    cases z <;> simp

  instance : SubstMapId Ty Ty where
    apply_id := by subst_solve_id

  instance : SubstMapStable Ty Ty where
    apply_stable := by subst_solve_stable

  instance : SubstMapRenComposeLeft Ty Ty where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight Ty Ty where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose Ty Ty where
    apply_compose := by subst_solve_compose

----------------------------------------------------------------------------------------------------
---- Term setup
----------------------------------------------------------------------------------------------------
  @[coe]
  def Term.from_action : Action Term -> Term
  | re y => var y
  | su t => t

  @[simp, grind =]
  theorem Term.from_action_id {n} : from_action (+0σ.act n) = var n := by
    simp [from_action]

  @[simp, grind =]
  theorem Term.from_action_succ {n} : from_action (+1σ.act n) = var (n + 1) := by
    simp [from_action]

  @[simp, grind =]
  theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

  @[simp, grind =]
  theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

  instance instCoe_SubstActionTerm_Term : Coe (Action Term) Term where
    coe := Term.from_action

  @[simp]
  def Term.Ty.rmap (r : Ren Ty) : Term -> Term
  | #x => #x
  | app t1 t2 => (rmap r t1) • (rmap r t2)
  | λ[A] t => λ[A⟨r⟩] rmap r t
  | t1 •[t2] => rmap r t1 •[t2⟨r⟩]
  | Λ t => Λ rmap r.lift t

  instance : RenMap Term Ty where
    rmap := Term.Ty.rmap

  @[simp, grind =]
  theorem Term.Ty.ren_var {x} {r : Ren Ty} : (#x)⟨r⟩ = #x := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.Ty.ren_app {t1 t2} {r : Ren Ty} : (t1 • t2)⟨r⟩ = t1⟨r⟩ • t2⟨r⟩ := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.Ty.ren_lam {A t} {r : Ren Ty} : (λ[A] t)⟨r⟩ = λ[A⟨r⟩] t⟨r⟩ := by
    simp [RenMap.rmap]

 @[simp, grind =]
  theorem Term.Ty.ren_tapp {t1 t2} {r : Ren Ty} : (t1 •[t2])⟨r⟩ = t1⟨r⟩ •[t2⟨r⟩] := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.Ty.ren_tlam {t} {r : Ren Ty} : (Λ t)⟨r⟩ = Λ t⟨r.lift⟩ := by
    simp [RenMap.rmap]

  instance : RenMapId Term Ty where
    apply_id := by subst_solve_id

  instance : RenMapCompose Term Ty where
    apply_compose := by subst_solve_compose

  @[simp]
  def Term.rmap (r : Ren Term) : Term -> Term
  | #x => #(r.act x)
  | app t1 t2 => rmap r t1 • rmap r t2
  | λ[A] t => λ[A] rmap r.lift t
  | t1 •[t2] => rmap r t1 •[t2]
  | Λ t => Λ rmap r t

  instance : RenMap Term Term where
    rmap := Term.rmap

  @[simp, grind =]
  theorem Term.ren_var {x} {r : Ren Term} : (Term.var x)⟨r⟩ = .var (r.act x) := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.ren_app {t1 t2} {r : Ren Term} : (t1 • t2)⟨r⟩ = t1⟨r⟩ • t2⟨r⟩ := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.ren_lam {A t} {r : Ren Term} : (λ[A] t)⟨r⟩ = λ[A] t⟨r.lift⟩ := by
    simp [RenMap.rmap]

 @[simp, grind =]
  theorem Term.ren_tapp {t1 t2} {r : Ren Term} : (t1 •[t2])⟨r⟩ = t1⟨r⟩ •[t2] := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem Term.ren_tlam {t} {r : Ren Term} : (Λ t)⟨r⟩ = Λ t⟨r⟩ := by
    simp [RenMap.rmap]

  instance : RenMapId Term Term where
    apply_id := by subst_solve_id

  instance : RenMapCompose Term Term where
    apply_compose := by subst_solve_compose

  @[simp]
  def Term.Ty.smap (σ : Subst Ty) : Term -> Term
  | #x => #x
  | app t1 t2 => smap σ t1 • smap σ t2
  | λ[A] t => λ[A[σ]] smap σ t
  | t1 •[t2] => smap σ t1 •[t2[σ]]
  | Λ t => Λ smap σ.lift t

  instance : SubstMap Term Ty where
    smap := Term.Ty.smap

  @[simp, grind =]
  theorem Term.Ty.subst_var {x} {σ : Subst Ty} : (#x)[σ] = #x := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.Ty.subst_app {t1 t2} {σ : Subst Ty} : (t1 • t2)[σ] = t1[σ] • t2[σ] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.Ty.subst_lam {A t} {σ : Subst Ty} : (λ[A] t)[σ] = λ[A[σ]] t[σ] := by
    simp [SubstMap.smap]

 @[simp, grind =]
  theorem Term.Ty.subst_tapp {t1 t2} {σ : Subst Ty} : (t1 •[t2])[σ] = t1[σ] •[t2[σ]] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.Ty.subst_tlam {t} {σ : Subst Ty} : (Λ t)[σ] = Λ t[σ.lift] := by
    simp [SubstMap.smap]

  instance : SubstMapId Term Ty where
    apply_id := by subst_solve_id

  instance : SubstMapStable Term Ty where
    apply_stable := by subst_solve_stable

  instance : SubstMapRenComposeLeft Term Ty where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight Term Ty where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose Term Ty where
    apply_compose := by subst_solve_compose

  @[simp]
  def Term.smap (σ : Subst Term) : Term -> Term
  | #x => σ.act x
  | app t1 t2 => smap σ t1 • smap σ t2
  | λ[A] t => λ[A] smap σ.lift t
  | t1 •[t2] => smap σ t1 •[t2]
  | Λ t => Λ smap (σ ◾ Ren.succ Ty) t

  instance : SubstMap Term Term where
    smap := Term.smap

  @[simp, grind =]
  theorem Term.subst_var {x} {σ : Subst Term} : (Term.var x)[σ] = σ.act x := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.subst_app {t1 t2} {σ : Subst Term} : (t1 • t2)[σ] = t1[σ] • t2[σ] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.subst_lam {A t} {σ : Subst Term} : (λ[A] t)[σ] = λ[A] t[σ.lift] := by
    simp [SubstMap.smap]

 @[simp, grind =]
  theorem Term.subst_tapp {t1 t2} {σ : Subst Term} : (t1 •[t2])[σ] = t1[σ] •[t2] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem Term.subst_tlam {t} {σ : Subst Term} : (Λ t)[σ] = Λ t[σ ◾ Ren.succ Ty] := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.from_action_compose {x : Nat} {σ τ : Subst Term}
    : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
  := by
    simp [from_action, Subst.compose]
    generalize zdef : σ.act x = z
    cases z <;> simp [from_action]

  @[simp]
  theorem Term.from_action_hcompose {x : Nat} {σ : Subst Term} {τ : Subst Ty}
    : (from_action (σ.act x))[τ] = from_action ((σ ◾ τ).act x)
  := by
    simp [from_action]
    generalize zdef : σ.act x = z
    cases z <;> simp

  @[simp]
  theorem Term.from_action_compose_ren {x : Nat} {σ : Subst Term} {r : Ren Term}
    : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
  := by
    simp [Term.from_action]
    generalize zdef : σ.act x = z
    cases z <;> simp

  @[simp]
  theorem Term.from_action_hcompose_ren {x : Nat} {σ : Subst Term} {r : Ren Ty}
    : (from_action (σ.act x))⟨r⟩ = from_action ((σ ◾ r).act x)
  := by
    simp [Term.from_action]
    generalize zdef : σ.act x = z
    cases z <;> simp

  instance : SubstMapRenCommute Term Ty where
    apply_commute_ren_subst := by subst_solve_compose
    apply_commute_ren_ren := by subst_solve_compose

  instance : SubstMapRenHetCompose Term Ty where
    apply_hcompose_ren := by subst_solve_compose

  instance : SubstMapHetCompose Term Ty where
    apply_hcompose := by subst_solve_compose

  instance : SubstMapId Term Term where
    apply_id := by subst_solve_id

  -- instance : SubstMapStable Term Term where
  --   apply_stable := by
  --     intro r σ h
  --     funext; case _ t =>
  --     induction t generalizing r σ
  --     all_goals simp [*] at *; try simp +instances [*]
  --     all_goals try solve | rw [Subst.apply_stable h]
  --     all_goals try solve | (rw [<-h]; simp +instances [Ren.to])
  --     all_goals try repeat funext; grind
  --     --subst_solve_stable

  instance : SubstMapRenComposeLeft Term Term where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight Term Term where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose Term Term where
    apply_compose := by subst_solve_compose

end Examples.SystemF
