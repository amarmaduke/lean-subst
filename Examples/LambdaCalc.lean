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

  @[simp]
  theorem Term.from_action_id {n} : from_action (+0 n) = var n := by
    simp [from_action, Subst.id]

  @[simp]
  theorem Term.from_action_succ {n} : from_action (+1 n) = var (n + 1) := by
    simp [from_action, Subst.succ]

  @[simp]
  theorem Term.from_acton_re {n} : from_action (re n) = var n := by simp [from_action]

  @[simp]
  theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

  instance instCoe_SubstActionTerm_Term : Coe (Subst.Action Term) Term where
    coe := Term.from_action

  @[simp]
  def smap (k : Subst.Kind) (lf : Subst.Lift Term k) (f : SplitSubst Term k) : Term -> Term
  | .var x =>
    match k with
    | .re => .var (f x)
    | .su => f x
  | t1 :@ t2 => smap k lf f t1 :@ smap k lf f t2
  | :λ t => :λ smap k lf (lf f) t

  instance SubstMap_Term : SubstMap Term where
    smap := smap

  @[simp]
  theorem subst_var {x} {σ : Subst Term} : (.var x)[σ] = σ x := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_app {t1 t2 σ} : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_lam {t σ} : (:λ t)[σ] = :λ t[σ.lift] := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem Term.from_action_compose {x} {σ τ : Subst Term}
    : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
  := by
    simp [Term.from_action, Subst.compose]
    generalize zdef : σ x = z
    cases z <;> simp [Term.from_action]

  theorem apply_id {t : Term} : t[+0] = t := by
    induction t
    all_goals (simp at * <;> try simp [*])

  theorem apply_stable (r : Ren) (σ : Subst Term)
    : r = σ -> Ren.apply r = Subst.apply σ
  := by solve_stable r, σ

  instance SubstMapStable_Term : SubstMapStable Term where
    apply_id := apply_id
    apply_stable := apply_stable

  theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
    solve_compose Term, s, σ, τ

  instance SubstMapCompose_Term : SubstMapCompose Term where
    apply_compose := apply_compose

end LeanSubst.Examples.LambdaCalc
