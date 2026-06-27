import LeanSubst
import Lean.Elab.Tactic
import LeanSubst.Automation.Attributes
import Qq
import Aesop

namespace Examples.LambdaCalc
  open LeanSubst

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term

  prefix:100 ":λ " => Term.lam
  infixl:65 " :@ " => Term.app

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
  def rmap (r : Ren Term) : Term -> Term
  | .var x => .var (r.act x)
  | t1 :@ t2 => rmap r t1 :@ rmap r t2
  | :λ t => :λ rmap r.lift t

  def rmap' (r : Ren Term) : Term → Term
  | Term.var x => Term.var (r.act x)
  | Term.app t1 t2 => Term.app (rmap r t1) (rmap r t2)
  | Term.lam t => Term.lam (rmap r.lift t)

  instance : RenMap Term Term where
    rmap := rmap

  @[simp, grind =]
  theorem ren_var {x} {r : Ren Term} : (Term.var x)⟨r⟩ = .var (r.act x) := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem ren_app {t1 t2} {r : Ren Term} : (t1 :@ t2)⟨r⟩ = t1⟨r⟩ :@ t2⟨r⟩ := by
    simp [RenMap.rmap]

  @[simp, grind =]
  theorem ren_lam {t} {r : Ren Term} : (:λ t)⟨r⟩ = :λ t⟨r.lift⟩ := by
    simp [RenMap.rmap]

  instance : RenMapId Term Term where
    apply_id := by subst_solve_id

  instance : RenMapCompose Term Term where
    apply_compose := by subst_solve_compose

  @[simp]
  def smap (σ : Subst Term) : Term -> Term
  | .var x => σ.act x
  | t1 :@ t2 => smap σ t1 :@ smap σ t2
  | :λ t => :λ smap σ.lift t

  instance SubstMap_Term : SubstMap Term Term where
    smap := smap

  @[simp, grind =]
  theorem subst_var {x} {σ : Subst Term} : (Term.var x)[σ] = σ.act x := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem subst_app {t1 t2} {σ : Subst Term} : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by
    simp [SubstMap.smap]

  @[simp, grind =]
  theorem subst_lam {t} {σ : Subst Term} : (:λ t)[σ] = :λ t[σ.lift] := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.from_action_compose {x : Nat} {σ τ : Subst Term}
    : (from_action (Subst.act σ x))[τ] = from_action ((σ ∘ τ).act x)
  := by
    simp [from_action, Subst.compose]
    generalize zdef : σ.act x = z
    cases z <;> simp [from_action]

  @[simp]
  theorem Term.from_action_compose_ren {x : Nat} {σ : Subst Term} {r : Ren Term}
    : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
  := by
    simp [Term.from_action]
    generalize zdef : σ.act x = z
    cases z <;> simp

  instance : SubstMapId Term Term where
    apply_id := by subst_solve_id

  instance : SubstMapStable Term Term where
    apply_stable := by subst_solve_stable

  instance : SubstMapRenComposeLeft Term Term where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight Term Term where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose Term Term where
    apply_compose := by subst_solve_compose

end Examples.LambdaCalc


namespace Examples.LambdaCalcAutomation
  open Lean Elab Tactic Meta LeanSubst Command Aesop

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term
  deriving BEq

  prefix:100 ":λ " => Term.lam
  infixl:65 " :@ " => Term.app

  attribute [leansubst_var] Term.var
  attribute [leansubst_binder] Term.lam

  def getConstructors (typeName : Name) : MetaM (List Name) := do
    let env ← getEnv
    match env.find? typeName with
    | some (.inductInfo val) => return val.ctors
    | _ => throwError "Not an inductive type: {typeName}"

  def isVar (ctor : Name) : MetaM Bool := do
    let env ← getEnv
    pure $ leanSubstVar.hasTag env ctor

  def getVarCtors (type : Name) : MetaM (List Name) := do
    let ctors ← getConstructors type
    List.filterM (isVar) ctors

  def isBinder (ctor : Name) : MetaM Bool := do
    let env ← getEnv
    pure $ leanSubstBinder.hasTag env ctor

  def getBinderCtors (type : Name) : MetaM (List Name) := do
    let ctors ← getConstructors type
    List.filterM (isBinder) ctors

  def getNonTaggedCtors (type : Name) : MetaM (List Name) := do
    let ctors ← getConstructors type
    List.filterM (fun n => do pure (¬ (← isVar n) ∧ ¬ (← isBinder n))) ctors

  #eval show MetaM Unit from do
    let lctx ← getLCtx
    let ctors ← getConstructors ``Term
    for ctor in ctors do
      let isVar ← isVar ctor
      let isBinder ← isBinder ctor
      if isVar then
        IO.println s!"{ctor} is a var"
      else if isBinder then
        IO.println s!"{ctor} is a binder"
      else
        IO.println s!"{ctor} is neither a var nor a binder"

    _ := lctx.addDecl
/-
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
-/
  def getForallBinderTypes : Expr → List Expr
    | .forallE _ t b _ => t :: getForallBinderTypes b
    | _ => []

  elab "#leansubst_autogen" ty:ident : command => do
    let tyName := ty.raw.getId
    let tyStr := tyName.toString
    let tyNameGlobal ← Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw

    let qualify str := mkIdent $ .str tyName str
    let pairWithTypes names : CommandElabM (List (Name × Expr)) :=
      List.mapM
        (fun name => do pure ⟨name, (← getConstInfo name).type⟩)
        names

    let xN (n : Nat) := mkIdent (.mkStr1 $ s!"x{n}")
    let xN_tm (n : Nat) : TSyntax `term := mkIdent (.mkStr1 $ s!"x{n}")
    let x := mkIdent `x
    let r := mkIdent `r
    let n := mkIdent `n
    let t := mkIdent `t

    let varCtorNames ← liftCoreM $ runMetaMAsCoreM $ getVarCtors tyNameGlobal
    let varName := varCtorNames[0]!
    let varType := (← getConstInfo varName).type
    let var := mkIdent varName

    let binderCtorNames ← liftCoreM $ runMetaMAsCoreM $ getBinderCtors tyNameGlobal
    let binderCtors := List.map mkIdent binderCtorNames

    let nonTaggedCtorNames ← liftCoreM $ runMetaMAsCoreM $ getNonTaggedCtors tyNameGlobal
    let nonTaggedCtors := List.map mkIdent nonTaggedCtorNames
    let nonTaggedCtorsWithTypes : List (Name × Expr) ← pairWithTypes nonTaggedCtorNames

    let from_action := qualify "from_action"
    elabCommand $ ← `(
      @[coe]
      def $from_action : Action $ty → $ty
      | re y => $var y
      | su t => t
    )

    let from_action_id := qualify "from_action_id"
    elabCommand $ ← `(
      @[simp, grind =]
      theorem $from_action_id {$n} : $from_action (+0σ.act $n) = $var $n := by
        simp [$from_action:ident]
    )

    let from_action_succ := qualify "from_action_succ"
    elabCommand $ ← `(
      @[simp, grind =]
      theorem $from_action_succ {$n} : $from_action (+1σ.act $n) = $var ($n + 1) := by
        simp [$from_action:ident]
    )

    let from_action_re := qualify "from_action_re"
    elabCommand $ ← `(
      @[simp, grind =]
      theorem $from_action_re {$n} : $from_action (re $n) = $var $n := by
        simp [$from_action:ident]
    )

    let from_action_su := qualify "from_action_su"
    elabCommand $ ← `(
      @[simp, grind =]
      theorem $from_action_su {$t} : $from_action (su $t) = $t := by
        simp [$from_action:ident]
    )

    let instCoe_SubstActionTy_Ty := mkIdent $ .mkStr1 s!"instCoe_SubstAction{tyStr}_{tyStr}"
    elabCommand $ ← `(
      instance $instCoe_SubstActionTy_Ty:ident : Coe (Action $ty) $ty where
        coe := $from_action
    )

    let rmap := qualify "rmap"
    let handleNonTaggedCtor : Name × Expr → CommandElabM (TSyntax `Lean.Parser.Term.matchAlt) := fun ⟨ctorName, type⟩ ↦ do
      let ctor := mkIdent ctorName
      let argTypes := getForallBinderTypes type

      let lhs : Array (TSyntax `term) := List.toArray $ List.map xN_tm $ List.range (List.length argTypes)

      let blah := isDefEq
      let lhs_types := Array.zip lhs argTypes.toArray
      let rhs : Array (TSyntax `term) ←
        Array.mapM
          (fun ⟨t, ty⟩ ↦ do
            let defEq ← liftCoreM $ runMetaMAsCoreM $ isDefEqGuarded ty (Expr.const tyNameGlobal [])
            if defEq then `($rmap $r $t) else `($t))
          lhs_types
      `(Parser.Term.matchAltExpr| | $ctor $lhs* => $ctor $rhs*)
    let nonTaggedCases := List.toArray $ ← List.mapM (handleNonTaggedCtor) nonTaggedCtorsWithTypes

    let varCase : (TSyntax `Lean.Parser.Term.matchAlt) ←
      `(Parser.Term.matchAltExpr| | $var $x => $var ($(r).act $x))

    let defaultPattern ← `(_)
    let defaultCase ← `(sorry)
    let default ← `(Parser.Term.matchAltExpr| | $defaultPattern => $defaultCase)
    let rmap := qualify "rmap"

    elabCommand $ ← `(
      def $rmap ($r : Ren $ty) : $ty → $ty
        $[$nonTaggedCases:matchAlt]*
        $varCase:matchAlt
        $default:matchAlt
    )

/-
  @[simp]
  def rmap (r : Ren Term) : Term -> Term
  | .var x => .var (r.act x)
  | t1 :@ t2 => rmap r t1 :@ rmap r t2
  | :λ t => :λ rmap r.lift t
-/

  #leansubst_autogen Term

  #print Term.from_action

  #print Term.from_action_id

  #print Term.from_action_succ

  #print Term.from_action_su

  #print instCoe_SubstActionTerm_Term
  #check instCoe_SubstActionTerm_Term.coe

  #print Term.rmap

end Examples.LambdaCalcAutomation
