import Lean.Elab.Tactic
import Qq
import Aesop

/- # Experiment 1 -/

namespace Experiment1
  open Lean Elab Tactic Meta Aesop Command

  def tacticMToCommandM {α} (tac : TacticM α) (mvarExpr : Option Expr := none) : CommandElabM α := do
    if let some mvarExpr := mvarExpr then
      liftTermElabM $ runTacticMAsTermElabM mvarExpr.mvarId! $ tac
    else
      let newMVarExpr ← liftTermElabM $ mkFreshExprMVar none
      liftTermElabM $ runTacticMAsTermElabM newMVarExpr.mvarId! $ tac

  elab "#thmtest" ty:ident : command => do
    let tyName ← liftCoreM $ realizeGlobalConstNoOverload ty.raw
    let ns ← getCurrNamespace

    -- def myId : ty → ty | x => x
    let def_myId_name := .mkStr3 ns.toString tyName.toString "myId"
    IO.println s!"{def_myId_name}"
    let def_myId_type ← liftTermElabM $ Term.elabType (← `($ty → $ty))
    let def_myId ← liftTermElabM $ Term.elabTermEnsuringType (← `(fun x : $ty => x)) (some def_myId_type)
    let def_myId_decl :=
      Declaration.defnDecl (
        mkDefinitionValEx
          def_myId_name
          []
          def_myId_type
          def_myId
          ReducibilityHints.abbrev
          DefinitionSafety.safe
          [])
    liftTermElabM $ addAndCompile def_myId_decl

    -- theorem my_id_thm : (n : ty) → my_id n = n
    -- let thm_myId_name := .str tyName "myId_thm"
    -- let thm_myId ← tacticMToCommandM $ Term.elabType (← `((n : $ty) → $(mkIdent def_myId_name) n = n))
    -- let newMVarExpr ← liftTermElabM $ mkFreshExprMVar (type? := some def_myId_type)
    -- liftCoreM $ runMetaMAsCoreM (do let _ ← runTactic newMVarExpr.mvarId! (← `(tactic| grind)))
    -- let proof ← liftTermElabM $ instantiateMVars newMVarExpr
    -- let fromActionIdDecl :=
    --   Declaration.thmDecl (
    --     mkTheoremValEx
    --       thm_myId_name
    --       []
    --       thm_myId
    --       proof
    --       [])
    -- liftTermElabM $ addAndCompile fromActionIdDecl

  #thmtest Nat

  #check Nat.myId

  #eval Experiment1.Nat.myId 1

end Experiment1

/- # Experiment 2 -/

namespace Experiment2
  open Lean Elab Command

  elab "#elabtest" ty:ident : command => do
    let tyName := ty.raw.getId
    let myId_ident := mkIdentFrom ty $ .str tyName "myId"
    let myId_thm_ident := mkIdentFrom ty $ .str tyName "myId_thm"
    elabCommand $ ← `(
      @[simp]
      def $(myId_ident) : $ty -> $ty
      | x => x

      theorem $(myId_thm_ident) (n : $ty) : $myId_ident n = n := by
        simp [$myId_ident:ident]
    )

  inductive Hi
  | Blah

  #elabtest Hi

  #check Hi.myId

  #eval Hi.myId Hi.Blah

  #check Hi.myId_thm Hi.Blah

  #elabtest Nat

  #check Nat.myId

  #eval Nat.myId 0

  #check Nat.myId_thm 0

end Experiment2
namespace Question
  open Lean Elab Tactic Meta Command Aesop

  elab "#test" : command => do
    let zeroCase ← `(Parser.Term.matchAltExpr| | 0 => 0)
    let succCase ← `(Parser.Term.matchAltExpr| | .succ n => n)
    elabCommand $ ← `(
      def $(mkIdent (.mkStr1 "myFun")) : Nat → Nat
      $zeroCase:matchAlt
      $succCase:matchAlt -- unexpected token ')'; expected ':=', 'where' or '|'
    )

  #test

  #eval myFun 0
  #eval myFun 1
  #eval myFun 2

end Question
