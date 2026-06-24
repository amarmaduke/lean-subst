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

  def isVar (env : Environment) (ctor : Name) : Bool := leanSubstVar.hasTag env ctor

  def getVarCtors (env : Environment) (type : Name) : MetaM (List Name) := do
    let ctors ← getConstructors type
    return (List.filter (isVar env) ctors)

  def isBinder (env : Environment) (ctor : Name) : Bool := leanSubstBinder.hasTag env ctor

  def getBinderCtors (env : Environment) (type : Name) : MetaM (List Name) := do
    let ctors ← getConstructors type
    return (List.filter (isBinder env) ctors)

  #print Term.from_action

  #eval show MetaM Unit from do
    let env ← getEnv
    let lctx ← getLCtx
    let ctors ← getConstructors ``Term
    for ctor in ctors do
      let isVar := isVar env ctor
      let isBinder := isBinder env ctor
      if isVar then
        IO.println s!"{ctor} is a var"
      else if isBinder then
        IO.println s!"{ctor} is a binder"
      else
        IO.println s!"{ctor} is neither a var nor a binder"

    _ := lctx.addDecl

/-
structure MkMatcherInput where
  matcherName : Name
  matchType   : Expr
  discrInfos  : Array DiscrInfo
  lhss        : List AltLHS
  isSplitter  : Option Overlaps := none

-/
  open Lean Elab Command in
  elab "#my_cmd" : command => Command.liftTermElabM do
    let ctx: LocalContext ← getLCtx
    let name := ctx.getUnusedName (.mkSimple "abcd")
    -- how to add `name` as a new, free variable?
    let fDecl := .inductDecl [] 0 [{ name, type := .sort 0, ctors := [] }] false
    (addDecl fDecl)

  #my_cmd

  #check abcd


  open Lean Elab Tactic Meta Match Qq in
  elab "#test0" : command => Command.liftTermElabM do
    -- Want to register new definition:
    -- def foo : Nat → Nat | x => x

    let matcher ← mkMatcher {
      matcherName := ← mkAuxDeclName `foo,
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

    let motive : Q(Nat → Type) := q(fun _ ↦ Nat → Nat)
    let case : Q(Nat → Nat → Nat) := q(fun _ x ↦ x)
    let func := mkAppN matcher.matcher #[motive, q(0), case]
    let func ← instantiateMVars func

    let typeExpr := q(Nat → Nat)
    let ctx ← getLCtx
    let newDecl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          (ctx.getUnusedName `foo)
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

  #test0

  #check foo

  #eval foo 3


  elab "#test1" : command => Command.liftTermElabM do
    let lctx ← getLCtx
    let matcher ← mkMatcher {
      matcherName := ← mkAuxDeclName `blah,
      matchType := q(Action Term → Term),
      discrInfos := #[{}],
      lhss := [
        ← withLocalDeclDQ `y q(Nat) fun y ↦ return {
          ref := ← getRef
          fvarDecls := ← [y].mapM (·.fvarId!.getDecl)
          patterns := [
            .ctor ``re [0] [q(Term)] [.var y.fvarId!]
          ]
        },
        ← withLocalDeclDQ `t q(Term) fun t ↦ return {
          ref := ← getRef
          fvarDecls := ← [t].mapM (·.fvarId!.getDecl)
          patterns := [
            .ctor ``su [0] [q(Term)] [.var t.fvarId!]
          ]
        }

      ]
    }
    matcher.addMatcher
    Lean.logInfo matcher.matcher

    let motive : Q(Action Term → Type) := q(fun _ ↦ Term)
    let case_re : Q((y : Nat) → Term) := q(fun y ↦ Term.var y)
    let case_su : Q((t : Term) → Term) := q(fun t ↦ t)
    let func := mkAppN matcher.matcher #[motive, case_re, case_su]

    let typeExpr := q(Action Term → Term)
    let newDecl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          (`blah1)
          []
          typeExpr
          func
          ReducibilityHints.abbrev
          DefinitionSafety.safe
          [])

    dbg_trace s!"func: {func}"
    -- Lean.compileDecl newDecl
    -- Lean.addAndCompile newDecl
    Lean.addAndCompile newDecl

  #test1

  #eval blah1 (re 1)

  elab "#test2" : command => do
    Command.elabEvalCore
      false
      Syntax.missing
      (← `(discard do (Command.elabCommand $ ← `(
        @[coe]
        def blah2 : Action Term -> Term
        | re y => Term.var y
        | su t => t
      ))))
      (mkApp (mkConst ``Command.CommandElabM) (mkConst ``Unit))

  #test2

  #check blah2

  open Lean.Elab.Command in run_cmd
    elabCommand $ ← `(
      @[coe]
      def blah3 : Action Term -> Term
      | re y => Term.var y
      | su t => t
    )

  #check blah3


end Examples.LambdaCalcAutomation
