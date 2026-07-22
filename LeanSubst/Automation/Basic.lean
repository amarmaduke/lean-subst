import LeanSubst
import Lean.Elab.Tactic
import Lean.Elab.Term.TermElabM
import LeanSubst.Automation.Attributes
import Aesop

namespace Automation
  open Lean Elab Tactic Meta LeanSubst Command Aesop

  def r1 : Ren Nat := sorry
  def r2 : Ren Bool := sorry

  #eval do
    let stx1 ← ``(r1)
    let stx2 ← ``(r2)

    let ⟨expr1, _⟩ ← Term.TermElabM.run $ Term.elabTerm stx1 none
    let ⟨expr2, _⟩ ← Term.TermElabM.run $ Term.elabTerm stx2 none

    let type1 ← inferType expr1
    let type2 ← inferType expr2

    let type1' := match type1 with
    | .app _ ty => some ty
    | _ => none
    let type2' := match type2 with
    | .app _ ty => some ty
    | _ => none

    dbg_trace s!"{[type1', type2']}"


  def getConstructors (typeName : Name) : MetaM (List Name) := do
    match (← getEnv).find? typeName with
    | some (.inductInfo val) => return val.ctors
    | _ => throwError "Not an inductive type: {typeName}"

  def isVar (ctor : Name) : MetaM Bool := do
    pure $ leanSubstVar.hasTag (← getEnv) ctor

  def getVarCtors (type : Name) : MetaM (List Name) := do
    List.filterM (isVar) (← getConstructors type)

  def getBinderParam (ctor : Name) : MetaM (Option Nat) := do
    pure (leanSubstBinder'.getParam? (← getEnv) ctor)

  def isBinder (ctor : Name) : MetaM Bool := do
    if let some _ := ← getBinderParam ctor then pure true else pure false

  def getBinderCtors (type : Name) : MetaM (List (Name × Nat)) := do
    (← getConstructors type).filterMapM
      (fun ctor ↦ do if let some i := ← getBinderParam ctor then pure $ some ⟨ctor, i⟩ else pure none)

  def getNonTaggedCtors (type : Name) : MetaM (List Name) := do
    List.filterM (fun n => do pure (¬ (← isVar n) ∧ ¬ (← isBinder n))) (← getConstructors type)

  def mapFst {α β} (ℓ : List (α × β)) := ℓ.map Prod.fst

  def mapSnd {α β} (ℓ : List (α × β)) := ℓ.map Prod.snd

  def getForallBinderTypes : Expr → List Expr
  | .forallE _ t b _ => t :: getForallBinderTypes b
  | _ => []

  inductive MapType
  | is_rmap
  | is_smap

  elab "#leansubst_autogen" ty:ident : command => do
    -- Setup --
    let tyName := ty.raw.getId
    let tyStr := tyName.toString
    let tyNameGlobal ← Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw

    let blah := Term.TermElabM.run $ Term.elabTypeOf sorry none
    let blah2 := Term.elabTypeOf


    let isDefEqTy ty' := liftCoreM $ runMetaMAsCoreM $ isDefEqGuarded ty' (.const tyNameGlobal [])

    let qualify str := mkIdent $ .str tyName str
    let pairWithTypes names : CommandElabM (List (Ident × Expr)) :=
      List.mapM
        (fun name => do pure ⟨name, (← getConstInfo name.getId).type⟩)
        names

    let pairWithTypes' namesAndParams : CommandElabM (List (Ident × Expr × Nat)) :=
      List.mapM
        (fun ⟨name, i⟩ => do pure ⟨name, (← getConstInfo name.getId).type, i⟩)
        namesAndParams


    let xN (n : Nat) : TSyntax `term := mkIdent (.mkStr1 $ s!"x{n}")
    let xN' (n : Nat) : TSyntax `ident := mkIdent (.mkStr1 $ s!"x{n}")
    let x := mkIdent `x
    let z := mkIdent `z
    let r := mkIdent `r
    let n := mkIdent `n
    let t := mkIdent `t
    let σ := mkIdent `σ
    let τ := mkIdent `τ

    let identToTerm : Ident → CommandElabM (TSyntax `term) := fun x ↦ `($x:ident)

    let varCtorNames ← liftCoreM $ runMetaMAsCoreM $ getVarCtors tyNameGlobal
    let varName := varCtorNames[0]!
    let varType := (← getConstInfo varName).type
    let var := mkIdent varName

    let binderCtorNamesWithParams ← liftCoreM $ runMetaMAsCoreM $ getBinderCtors tyNameGlobal
    let binderCtorsWithParams : List (Ident × Nat) := binderCtorNamesWithParams.map (fun ⟨name, i⟩ ↦ ⟨mkIdent name, i⟩)
    let binderCtorsWithTypesAndParams ← pairWithTypes' binderCtorsWithParams

    let nonTaggedCtorNames ← liftCoreM $ runMetaMAsCoreM $ getNonTaggedCtors tyNameGlobal
    let nonTaggedCtors := nonTaggedCtorNames.map mkIdent
    let nonTaggedCtorsWithTypes ← pairWithTypes nonTaggedCtors

    let doVarComputation
      : (ty : Type) → ((ctor : Ident) → (varArg : Ident) → (otherArgs : List (Ident × Expr)) → CommandElabM ty)
        → CommandElabM ty := fun _ f ↦ do
      let argTypes := getForallBinderTypes varType
      let argIdents := (List.range $ argTypes.length).map xN'
      let argIdentsWithTypes := argIdents.zip argTypes
      if let some ⟨argIdent_hd, _⟩ := argIdentsWithTypes.head? then
        f var argIdent_hd (argIdents.tail.zip argTypes.tail)
      else
        throwAbortCommand -- TODO: better error?

    let doNonTaggedComputation
      : (ty : Type) → ((ctor : Ident) → (args : List (Ident × Expr)) → CommandElabM ty)
        → CommandElabM (List ty) := fun _ f ↦ do
      nonTaggedCtorsWithTypes.mapM (fun ⟨ctor, type⟩ ↦ do
        let argTypes := getForallBinderTypes type
        let argIdents := (List.range $ argTypes.length).map xN'
        f ctor $ argIdents.zip argTypes
      )

    let doBinderComputation
      : (ty : Type)
        → ((ctor : Ident) → (binderArgWithType : Ident × Expr) → (otherArgs : List (Ident × Expr)) → (binderPos : Nat) → CommandElabM ty)
        → CommandElabM (List ty) := fun _ f ↦ do
      binderCtorsWithTypesAndParams.mapM (fun ⟨ctor, type, i⟩ ↦ do
        let argTypes := getForallBinderTypes type
        let argIdents := (List.range $ argTypes.length).map xN'
        let argIdentsWithTypes := argIdents.zip argTypes
        if let some ⟨argIdent_hd, argType_hd⟩ := argIdentsWithTypes.head? then
          f ctor ⟨argIdent_hd, argType_hd⟩ (argIdents.tail.zip argTypes.tail) i
        else
          throwAbortCommand -- TODO: better error?
      )

    let mkBinderStx
      (ctor : Ident) (binderArg : TSyntax `term) (otherArgs : List $ TSyntax `term) (i : Nat) : CommandElabM $ TSyntax `term := do
      let beforeBinderArgs := (otherArgs.take i).toArray
      let afterBinderArgs := (otherArgs.drop i).toArray
      `($ctor $beforeBinderArgs* $binderArg $afterBinderArgs*)

    let mkBinderStx'
      (ctor : Ident) (binderArg : TSyntax `term) (otherArgs : List $ TSyntax `ident) (i : Nat) : CommandElabM $ TSyntax `term := do
      let beforeBinderArgs := (otherArgs.take i).toArray
      let afterBinderArgs := (otherArgs.drop i).toArray
      `($ctor $beforeBinderArgs* $binderArg $afterBinderArgs*)

    let mkBinderArgs
      (ty : Name) (binderArg : TSyntax ty) (otherArgs : List $ TSyntax ty) (i : Nat) : TSyntaxArray ty :=
      let beforeBinderArgs := (otherArgs.take i).toArray
      let afterBinderArgs := (otherArgs.drop i).toArray
      beforeBinderArgs ++ [binderArg] ++ afterBinderArgs

    -- from_action --
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

    -- Coe --
    let instCoe_SubstActionTy_Ty := mkIdent $ .mkStr1 s!"instCoe_SubstAction{tyStr}_{tyStr}"
    elabCommand $ ← `(
      instance $instCoe_SubstActionTy_Ty:ident : Coe (Action $ty) $ty where
        coe := $from_action
    )

    -- rmap and smap --
    let doMapStuff : MapType → CommandElabM Unit :=
      fun mapType ↦ do
        let leanSubstQualify s := .mkStr2 "LeanSubst" s
        let ⟨defIdent, typeIdent, instanceIdent, instanceFieldIdent, rσ, thmPfxStr⟩ : Ident × Ident × Ident × Ident × Ident × String :=
          match mapType with
          | .is_rmap =>
            ⟨qualify "rmap", mkIdent $ leanSubstQualify "Ren", mkIdent $ leanSubstQualify "RenMap", mkIdent $ .mkStr1 "rmap", r, "ren"⟩
          | .is_smap =>
            ⟨qualify "smap", mkIdent $ leanSubstQualify "Subst", mkIdent $ leanSubstQualify "SubstMap", mkIdent $ .mkStr1 "smap", σ, "subst"⟩

        let nonTaggedCases := List.toArray $ ← doNonTaggedComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor args ↦ do
          let rhs : List (TSyntax `term) ←
            List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($defIdent $rσ $t) else `($t)) args
          `(Parser.Term.matchAltExpr| | $ctor $((args.map Prod.fst).toArray)* => $ctor $(rhs.toArray)*)
        )

        let binderCases := List.toArray $ ← doBinderComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor ⟨binderIdent, _⟩ otherArgs i ↦ do
          let otherArgs := mapFst otherArgs
          let lhs ← mkBinderStx' ctor binderIdent otherArgs i
          let binderRhs ← `($defIdent $(rσ).lift $binderIdent)
          let rhs ← mkBinderStx' ctor binderRhs otherArgs i
          `(Parser.Term.matchAltExpr| | $lhs => $rhs)
        )

        let varCase := ← doVarComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor varIdent otherArgs ↦ do
          let lhs := List.cons varIdent (otherArgs.map Prod.fst)
          let rhsVar ← `($(rσ).act $varIdent)
          let rhsOther := otherArgs.tail.map Prod.fst
          let rhs := List.cons rhsVar $ ← rhsOther.mapM identToTerm
          match mapType with
          | .is_rmap => `(Parser.Term.matchAltExpr| | $ctor $(lhs.toArray)* => $ctor $(rhs.toArray)*)
          | .is_smap => `(Parser.Term.matchAltExpr| | $ctor $(lhs.toArray)* => $rhsVar)
        )

        elabCommand $ ← `(
          @[simp]
          def $defIdent ($rσ : $typeIdent:ident $ty) : $ty → $ty
            $varCase:matchAlt
            $[$nonTaggedCases:matchAlt]*
            $[$binderCases:matchAlt]*
        )

        let simpCall ← match mapType with
        | .is_rmap => `(tactic| simp [RenMap.rmap])
        | .is_smap => `(tactic| simp [SubstMap.smap])

        elabCommand $ ← `(
          instance : $instanceIdent:ident ($ty:ident) ($ty:ident) where
            $instanceFieldIdent:ident := $defIdent
        )

        _ ← doNonTaggedComputation Unit (fun ctor args ↦ do
          let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"

          let lhsArgs := mapFst args
          let lhs ← match mapType with
          | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
          | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

          let rhsArgs ← match mapType with
          | .is_rmap => List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($t⟨$rσ⟩) else `($t)) args
          | .is_smap => List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($t[$rσ]) else `($t)) args
          let rhs ← `($ctor $(rhsArgs.toArray)*)

          elabCommand $ ← `(
            @[simp, grind =]
            theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
              $simpCall:tactic
          )
        )

        _ ← doBinderComputation Unit (fun ctor ⟨binderArg, _⟩ otherArgs i ↦ do
          let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"
          let otherArgs := mapFst otherArgs

          let lhsArgs := mkBinderArgs `ident binderArg otherArgs i
          let lhs ← match mapType with
          | .is_rmap => `(($ctor $lhsArgs*)⟨$rσ⟩)
          | .is_smap => `(($ctor $lhsArgs*)[$rσ])

          let rhsBinder ← match mapType with
          | .is_rmap => `($binderArg⟨$(rσ).lift⟩)
          | .is_smap => `($binderArg[$(rσ).lift])
          let rhs ← mkBinderStx' ctor rhsBinder otherArgs i

          elabCommand $ ← `(
            @[simp, grind =]
            theorem $thmName {$lhsArgs*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
              $simpCall:tactic
          )
        )

        _ ← doVarComputation Unit (fun ctor varArg otherArgs ↦ do
          let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"
          let lhsArgs := varArg :: mapFst otherArgs
          let lhs ← match mapType with
          | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
          | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

          let rhsVar ← `($(rσ).act $varArg)
          let rhsOther ← List.mapM (fun ⟨t, _⟩ ↦ `($t)) otherArgs
          let rhsArgs := rhsVar :: rhsOther
          let rhs ← match mapType with
          | .is_rmap => `($ctor $(rhsArgs.toArray)*)
          | .is_smap => pure rhsVar

          elabCommand $ ← `(
            @[simp, grind =]
            theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
              $simpCall:tactic
          )
        )

    doMapStuff .is_rmap
    doMapStuff .is_smap

    -- from_action --
    let from_action_compose := qualify "from_action_compose"
    let from_action_compose_ren := qualify "from_action_compose_ren"
    elabCommand $ ← `(
      @[simp]
      theorem $from_action_compose {$x : Nat} {$σ $τ : Subst $ty}
        : ($from_action (Subst.act $σ $x))[$τ] = $from_action (($σ ∘ $τ).act $x)
      := by
        simp [$from_action:ident, Subst.compose]
        generalize zdef : $(σ).act $x = $z
        cases $z:ident <;> simp [$from_action:ident]

      @[simp]
      theorem $from_action_compose_ren {$x : Nat} {$σ : Subst $ty} {$r : Ren $ty}
        : ($from_action:ident ($(σ).act $x))⟨$r⟩ = $from_action:ident (($σ ∘ $r).act $x)
      := by
        simp [$from_action:ident]
        generalize zdef : $(σ).act $x = $z
        cases $z:ident <;> simp
    )

    -- instances --
    elabCommand $ ← `(
      instance : RenMapId $ty $ty where
        apply_id := by subst_solve_id

      instance : RenMapCompose $ty $ty where
        apply_compose := by subst_solve_compose

      instance : SubstMapId $ty $ty where
        apply_id := by subst_solve_id

      instance : SubstMapStable $ty $ty where
        apply_stable := by subst_solve_stable

      instance : SubstMapRenComposeLeft $ty $ty where
        apply_ren_compose_left := by subst_solve_compose

      instance : SubstMapRenComposeRight $ty $ty where
        apply_ren_compose_right := by subst_solve_compose

      instance : SubstMapCompose $ty $ty where
        apply_compose := by subst_solve_compose
    )

end Automation
