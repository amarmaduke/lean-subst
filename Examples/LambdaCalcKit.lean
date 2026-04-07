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
  def Term.ren_act (r : Nat -> Nat) : Term -> Term
  | .var x => .var (r x)
  | t => t

  @[simp]
  def Term.subst_act (σ : Nat -> Subst.Action Term) : Term -> Term
  | .var x => σ x
  | t => t

  class Kit (T : Type) (A : Type) where
    act (f : Nat -> A) : T -> T
    lift (f : Nat -> A) (k : Nat := 1) : Nat -> A

  @[simp]
  instance : Kit Term Nat where
    act := Term.ren_act
    lift f n := Ren.lift f n

  @[simp]
  instance [RenMap Term] : Kit Term (Subst.Action Term) where
    act := Term.subst_act
    lift f n := Subst.lift f n

  @[simp]
  def kitmap {A} (σ : Nat -> A) [kit : Kit Term A] : Term -> Term
  | .var x => kit.act σ (.var x)
  | t1 :@ t2 => kitmap σ t1 :@ kitmap σ t2
  | :λ t => :λ kitmap (kit.lift σ) t

  @[simp]
  def rmap (r : Ren) : Term -> Term := kitmap r

  instance : RenMap Term where
    rmap := rmap

  @[simp]
  def smap (σ : Subst Term) : Term -> Term := kitmap σ

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

  theorem apply_id {t : Term} : t[+0] = t := by
    induction t
    all_goals (simp at * <;> try simp [*])

  instance : SubstMapId Term Term where
    apply_id := apply_id

  theorem apply_stable (r : Ren) (σ : Subst Term)
    : r = σ -> rmap r = smap σ
  := by subst_solve_stable r, σ

  instance : SubstMapStable Term where
    apply_stable := apply_stable

  theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
    subst_solve_compose Term, s, σ, τ


  instance : SubstMapCompose Term Term where
    apply_compose := apply_compose

end LeanSubst.Examples.LambdaCalc
