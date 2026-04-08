import LeanSubst

namespace LeanSubst.Examples.LambdaCalc

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term

  prefix:100 ":λ " => Term.lam
  infixl:65 " :@ " => Term.app

  @[coe]
  def Term.from_action : Subst.Action Term -> Term
  | re y => var y
  | su t => t

  @[simp, grind =]
  theorem Term.from_action_id {n} : from_action (+0 n) = var n := by
    simp [from_action, Subst.id]

  @[simp, grind =]
  theorem Term.from_action_succ {n} : from_action (+1 n) = var (n + 1) := by
    simp [from_action, Subst.succ]

  @[simp, grind =]
  theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

  @[simp, grind =]
  theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

  instance instCoe_SubstActionTerm_Term : Coe (Subst.Action Term) Term where
    coe := Term.from_action

  @[simp]
  def rmap (r : Ren) : Term -> Term
  | .var x => .var (r x)
  | t1 :@ t2 => rmap r t1 :@ rmap r t2
  | :λ t => :λ rmap r.lift t

  instance : RenMap Term where
    rmap := rmap

  @[simp, grind =]
  theorem ren_var {x} {r : Ren} : (Term.var x)⟨r⟩ = .var (r x) := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem ren_app {t1 t2} {r : Ren} : (t1 :@ t2)⟨r⟩ = t1⟨r⟩ :@ t2⟨r⟩ := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem ren_lam {t} {r : Ren} : (:λ t)⟨r⟩ = :λ t⟨r.lift⟩ := by
    simp [RenMap.rmap]

  instance : RenMapId Term where
    apply_id := by intro t; induction t <;> simp [*]

  instance : RenMapCompose Term where
    apply_compose := by intro t r1 r2; induction t generalizing r1 r2 <;> simp [*]

  @[simp]
  def smap (σ : Subst Term) : Term -> Term
  | .var x => σ x
  | t1 :@ t2 => smap σ t1 :@ smap σ t2
  | :λ t => :λ smap σ.lift t

  instance SubstMap_Term : SubstMap Term Term where
    smap := smap

  @[simp, grind =]
  theorem subst_var {x} {σ : Subst Term} : (Term.var x)[σ] = σ x := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem subst_app {t1 t2} {σ : Subst Term} : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem subst_lam {t} {σ : Subst Term} : (:λ t)[σ] = :λ t[σ.lift] := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.from_action_compose {x} {σ τ : Subst Term}
    : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
  := by
    simp [Term.from_action, Subst.compose]
    generalize zdef : σ x = z
    cases z <;> simp [Term.from_action]

  instance : SubstMapId Term Term where
    apply_id := by subst_solve_id

  instance : SubstMapStable Term where
    apply_stable := by subst_solve_stable

  instance : SubstMapRenComposeLeft Term Term where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight Term Term where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose Term Term where
    apply_compose := by subst_solve_compose

end LeanSubst.Examples.LambdaCalc
