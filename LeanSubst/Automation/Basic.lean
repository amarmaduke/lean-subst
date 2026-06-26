import LeanSubst
import Lean.Elab.Tactic
import LeanSubst.Automation.Attributes
import Qq

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
  open Lean Elab Tactic Meta LeanSubst Match Qq

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term
  deriving BEq

  prefix:100 ":λ " => Term.lam
  infixl:65 " :@ " => Term.app

  attribute [leansubst_var] Term.var
  attribute [leansubst_binder] Term.lam

  @[coe]
  def Term.from_action : Action Term -> Term
  | re y => var y
  | su t => t

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

  #print Term.from_action

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


  /- # Test 0 -/
  -- Uses q antiquotation to define the function, then Declaration.defnDecl to declare the function as a definition in the environment.

  elab "#test0" ty:ident : command => Command.liftTermElabM do
    let tyName ← realizeGlobalConstNoOverload ty.raw
    let func := mkApp q(fun ty : Type ↦ fun x : ty ↦ x) (.const tyName [])
    let typeExpr := q(Nat → Nat)
    let newDecl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          (`foo0)
          []
          typeExpr
          func
          ReducibilityHints.abbrev
          DefinitionSafety.safe
          [])
    Lean.addAndCompile newDecl
    -- Lean.compileDecl newDecl -- Tried this, doesn't register definition
    -- Lean.addDecl newDecl -- Tried this, same metavariable error

  #check foo0

  #test0 Nat

  #check foo0

  #eval foo0 3

  /- # Test 0'-/
  -- Uses mkMatcher to define the LHS patterns.

  elab "#test0'" : command => Command.liftTermElabM do
    -- Want to register new definition:
    -- def foo : Nat → Nat | x => x

    let matcher ← mkMatcher {
      matcherName := ← mkAuxDeclName `foo0',
      matchType := q(Nat → Nat),
      discrInfos := #[{}],
      lhss := [
        ← withLocalDeclDQ `x q(Nat) fun x ↦ return {
          ref := ← getRef
          fvarDecls := ← [x].mapM (·.fvarId!.getDecl)
          patterns := [
            .var x.fvarId!
          ]
        }
      ]
    }
    matcher.addMatcher
    Lean.logInfo matcher.matcher

    let motive : Q(Nat → Type) := q(fun _ ↦ Nat)
    let case : Q(Nat → Nat) := q(fun x ↦ x)
    let func := mkAppN matcher.matcher #[motive]
    let func ← instantiateMVars func


    let typeExpr := q(Nat → Nat)
    let ctx ← getLCtx
    let newDecl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          `foo0'
          []
          typeExpr
          func
          ReducibilityHints.abbrev
          DefinitionSafety.safe
          [])

    dbg_trace s!"func: {func}" -- func: _private.LeanSubst.Automation.Basic.0.foo_174.{?_uniq.24495} (fun (x : Nat) => Nat) (fun (x : Nat) => x)
    Lean.addAndCompile newDecl
    -- Lean.compileDecl newDecl -- Tried this, doesn't register definition
    -- Lean.addDecl newDecl -- Tried this, same metavariable error


  #test0'

  #check Nat.brecOn

  #check foo0'

  #eval foo0' 0


  /- # Test 1 -/
  -- Define actual from_action.

  elab "#test1" : command => Command.liftTermElabM do
    let name := `Term.foo
    let func := q(fun | (re x) => Term.var x | (su x) => x)
    let typeExpr := q(Action Term → Term)
    let newDecl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          name
          []
          typeExpr
          func
          ReducibilityHints.abbrev
          DefinitionSafety.safe
          [])

    Lean.addAndCompile newDecl

    let coeStx ← `(coe)
    Attribute.add `Term.from_action_auto `coe coeStx

  #test1

  #eval Term.foo (re 1)

  /- # Test 2 -/
  -- Name gets passed in; definition parametrized by name.
  /-
  @[simp, grind =]
  theorem Term.from_action_id {n} : from_action (+0σ.act n) = var n := by
    simp [from_action]
  -/

  elab "#test2" ty:ident : command => do
    let tyName ← Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw

    let varCtors ← Command.liftTermElabM $ getVarCtors tyName
    if let some varCtorName := varCtors[0]? then
      let varCtor : Expr := .const varCtorName []

      -- from_action
      let fromActionAutoName := Name.str tyName "from_action_auto"
      let fromActionType := mkApp q(fun term : Type ↦ Action term → term) (.const tyName [])
      let fromActionAuto' := q(fun term : Type ↦ fun varCtor : Nat → term ↦ fun | (re x) => varCtor x | (su x) => x)
      let fromActionAuto := mkAppN fromActionAuto' #[.const tyName [], varCtor]
      let fromActionDecl :=
        Declaration.defnDecl (
          mkDefinitionValEx
            fromActionAutoName
            []
            fromActionType
            fromActionAuto
            ReducibilityHints.abbrev
            DefinitionSafety.safe
            [])
      Command.liftTermElabM $ Lean.addAndCompile fromActionDecl

      -- from_action_id
      let fromActionIdAutoType :=
        mkAppN
          q(
            fun term : Type ↦
            fun varCtor : Nat → term ↦
            fun from_action : Action term → term ↦
            (n : Nat) → from_action (+0σ.act n) = varCtor n)
          #[.const tyName [], varCtor, Expr.const fromActionAutoName []]
      let newMVarExpr ← Command.liftTermElabM $ mkFreshExprMVar (type? := some fromActionIdAutoType)
      dbg_trace s!"new mvar: {newMVarExpr}"
      let _ ← Command.liftTermElabM $ Term.runTactic (newMVarExpr.mvarId!) (← `(by simp)) Term.TacticMVarKind.term
      let proof ← Command.liftTermElabM $ instantiateMVars newMVarExpr
      let fromActionIdDecl :=
        Declaration.thmDecl (
          mkTheoremValEx
            (.str tyName "from_action_id_auto")
            []
            fromActionIdAutoType
            proof
            []
        )

      Command.liftTermElabM $ Lean.addAndCompile fromActionIdDecl
    else
      throwUnsupportedSyntax -- need better error

  #test2 Term

  #print Term

  #check Term.from_action_auto

  #eval Term.from_action_auto (re 0)

  #check Term.from_action_id_auto


  elab "#stxtest" ty:ident : command => do
    Command.elabDeclaration $ ← `(
      def $(mkIdentFrom ty.raw $ Name.mkStr1 "myId") : $ty -> $ty
      | x => x
    )

  #stxtest Term

  #check myId

  open Lean.Elab.Command in run_cmd
    Command.elabCommand $ ← `(
      @[coe]
      def blah3 : Action Term -> Term
      | re y => Term.var y
      | su t => t
    )

  #check blah3


end Examples.LambdaCalcAutomation
