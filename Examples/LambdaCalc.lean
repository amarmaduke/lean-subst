import LeanSubst

namespace LeanSubst.Examples.LambdaCalc

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term

  instance instTerm_PrefixHash : PrefixHash Term where
    hash := Term.var

  namespace Term
    @[simp]
    theorem var_def {x} : Term.var x = #x := by
      simp [PrefixHash.hash]

    @[simp]
    theorem var_eq {x y} : (PrefixHash.hash (T := Term) x = #y) = (x = y) := by
      simp [-var_def, PrefixHash.hash]
  end Term

  prefix:100 ":λ" => Term.lam
  infixl:65 ":@" => Term.app

  @[simp]
  def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
  | .var x =>
    match f x with
    | .re y => #y
    | .su t => t
  | t1 :@ t2 => smap lf f t1 :@ smap lf f t2
  | :λ t => :λ smap lf (lf f) t

  instance SubstMap_Term : SubstMap Term where
    smap := smap

  instance HasSimpleVar_Term : HasSimpleVar Term where
    var := Term.var
    smap := by solve_simple_var_smap

  @[simp]
  theorem subst_var {x} {σ : Subst Term} : (#x)[σ] = match σ x with | .re y => #y | .su t => t := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_app {t1 t2 σ} : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_lam {t σ} : (:λ t)[σ] = :λ t[σ.lift] := by
    unfold Subst.apply; simp [SubstMap.smap]

  theorem apply_id {t : Term} : t[I] = t := by
    induction t
    all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst Term}
    : r.to = σ -> Ren.apply r = Subst.apply σ
  := by solve_stable r, σ

  instance SubstMapStable_Term : SubstMapStable Term where
    apply_id := apply_id
    apply_stable := apply_stable

  theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
    solve_compose Term, s, σ, τ

  instance SubstMapCompose_Term : SubstMapCompose Term where
    apply_compose := apply_compose

end LeanSubst.Examples.LambdaCalc
