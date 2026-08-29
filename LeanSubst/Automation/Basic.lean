import LeanSubst
import Lean.Elab.Tactic
import Lean.Elab.Term.TermElabM
import LeanSubst.Automation.Attributes
import Aesop

namespace Automation
  open Lean Elab Tactic Meta LeanSubst Command Aesop LeanSubstAttributes

  def getConstructors (typeName : Name) : MetaM (List Name) := do
    match (← getEnv).find? typeName with
    | some (.inductInfo val) => return val.ctors
    | _ => throwError "Could not get constructors of: {typeName}"


  def isVar (ctor : Name) : MetaM Bool := do
    pure $ leanSubstVar.hasTag (← getEnv) ctor

  def isNotVar (ctor : Name) : MetaM Bool := do
    pure $ ¬ leanSubstVar.hasTag (← getEnv) ctor

  def getNonVarConstructors (typeName : Name) : MetaM (List Name) := do
    match (← getEnv).find? typeName with
    | some (.inductInfo val) => val.ctors.filterM isNotVar
    | _ => throwError "Could not get constructors of: {typeName}"

  def getVarCtor (type : Name) : MetaM (Option Name) := do
    List.findM? (isVar) (← getConstructors type)

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

  def xN (n : Nat) : TSyntax `term := mkIdent (.mkStr1 $ s!"x{n}")
  def xN' (n : Nat) : TSyntax `ident := mkIdent (.mkStr1 $ s!"x{n}")
  def x := mkIdent `x
  def y := mkIdent `y
  def z := mkIdent `z
  def r := mkIdent `r
  def n := mkIdent `n
  def t := mkIdent `t
  def σ := mkIdent `σ
  def τ := mkIdent `τ

  def CtorArgBindData := List $ Term × Term

  inductive ArgData
  | binder : List (Term × Ident) → ArgData -- (Term × Ident) corresponds to ([num bound closure] × [type being bound])
  | var
  | none

  def getClosureFromArgData (ty : Ident) : ArgData → Option Term
  | .binder xs => (xs.find? (fun (_, ty') => BEq.beq ty' ty)).map (·.1)
  | _ => none

  def getCtorArgData (ctor : Name) (p : Nat) : CommandElabM $ ArgData := do
    if let some data := leanSubstBinder.getParam? (← getEnv) ctor then
      pure $ .binder $ data |> .filter (fun (_, _, p') => p' = p) |> .map (fun (t1, t2, _) => (t1, t2))
    else if ← liftCoreM $ runMetaMAsCoreM $ isVar ctor then
      pure .var
    else
      pure .none

  def numArgsInCtor (ctor : Name) : CommandElabM Nat := do
    let ctorType := (← getConstInfo ctor).type
    let argTypes := getForallBinderTypes ctorType
    pure $ argTypes.length

  def isBoundInCtorAtPos (A Bctor : Name) (pos : Nat) : CommandElabM Bool := do
    let data ← getCtorArgData Bctor pos
    if let .binder binds := data then
      binds.anyM (fun ⟨_, ty⟩ ↦ do liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm (mkIdent A) none) (← liftTermElabM $ Term.elabTerm ty none))
    else
      pure false

  def isBoundInCtor (A Bctor : Name) : CommandElabM Bool := do
    (List.range $ ← numArgsInCtor Bctor).anyM (fun pos ↦ isBoundInCtorAtPos A Bctor pos)

  -- Check if A is bound in B
  def isBoundIn (A B : Name) : CommandElabM Bool := do
    (← liftCoreM $ runMetaMAsCoreM $ getConstructors B).anyM (isBoundInCtor A)

  def mkCtorLhs (ctor : Name) : CommandElabM $ Term := do
    let ctorType := (← getConstInfo ctor).type
    let argTypes := getForallBinderTypes ctorType
    let argTypesWithData ←
      argTypes
      |> (.zip · (List.range $ List.length argTypes))
      |> List.mapM (fun (ty, p) ↦ do pure (ty, ← getCtorArgData ctor p, xN' p))
    let xs : List Ident := argTypesWithData.map (fun (_, _, x) ↦ x)
    `($(mkIdent ctor) $(xs.toArray)*)

  def mkCtorArgs (ctor : Name) : CommandElabM $ List Ident := do
    pure $ List.map xN' $ List.range $ (← numArgsInCtor ctor)

  def mkCtorRhs (f : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ctor : Name) : CommandElabM $ Term := do
    let ctorType := (← getConstInfo ctor).type
    let argTypes := getForallBinderTypes ctorType
    let argTypesWithData ←
      argTypes
      |> (.zip · (List.range $ List.length argTypes))
      |> List.mapM (fun (ty, p) ↦ do pure (ty, ← getCtorArgData ctor p, xN' p))
    let xs : List Ident := argTypesWithData.map (fun (_, _, x) ↦ x)
    let mappedXs ← (argTypesWithData.toArray.mapM (fun (ty, data, x) ↦ (f ty data x xs)))
    `($(mkIdent ctor) $mappedXs*)

  def mkCtorCase (f : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ctor : Name) : CommandElabM $ TSyntax `Lean.Parser.Term.matchAltExpr := do
    let lhs ← mkCtorLhs ctor
    let rhs ← mkCtorRhs f ctor
    `(Parser.Term.matchAltExpr| | $lhs => $rhs)

  def mkVarCtorRhs (f : List Ident → CommandElabM Term) (ctor : Name) : CommandElabM $ Term := do
    f $ ← mkCtorArgs ctor

  def mkVarCtorCase (f : List Ident → CommandElabM Term) (ctor : Name) : CommandElabM $ TSyntax `Lean.Parser.Term.matchAltExpr := do
    let lhs ← mkCtorLhs ctor
    let rhs ← mkVarCtorRhs f ctor
    `(Parser.Term.matchAltExpr| | $lhs => $rhs)

  def mkCtorEq (fLhs : Term → CommandElabM Term) (fRhs : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ctor : Name) : CommandElabM $ Term := do
    let lhs ← mkCtorLhs ctor >>= fLhs
    let rhs ← mkCtorRhs fRhs ctor
    `($lhs = $rhs)

  -- Need to give the option of handling the var case by doing more than just mapping each argument
  def mkAllCases (f : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ty : Name) (fVar : Option (List Ident → CommandElabM Term) := none) : CommandElabM $ TSyntaxArray `Lean.Parser.Term.matchAltExpr := do
    if let some fVar := fVar then
      let nonVarCtors ← liftCoreM $ runMetaMAsCoreM $ getNonVarConstructors ty
      let nonVarCases ← nonVarCtors.toArray.mapM (mkCtorCase f)
      if let some varCtor ← liftCoreM $ runMetaMAsCoreM $ getVarCtor ty then
        let varCase ← mkVarCtorCase fVar varCtor
        pure $ Array.append #[varCase] nonVarCases
      else throwError "ruh roh"
    else
      let ctors ← liftCoreM $ runMetaMAsCoreM $ getConstructors ty
      ctors.toArray.mapM (mkCtorCase f)

  def getTy (rσ : Ident) (tys : Array Ident) (ty : Ident) : CommandElabM Term := do
    let pos := tys.idxOf ty
    let mut stx ← `($rσ)
    for _ in List.range pos do
      stx ← `($stx.2)
    `($stx.1)

  def genTy (tys : List Ident) : CommandElabM Unit := do
    let ty := tys[0]!
    let tyName := ty.raw.getId
    let tyStr := tyName.toString
    let tyNameGlobal ← Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw

    dbg_trace s!"Generating {ty} with list {tys}"

    let tyArr ← `([$tys.toArray,*])
    let tysNamesGlobal ← tys.mapM (Command.liftCoreM $ realizeGlobalConstNoOverload ·.raw)

    let qualify str := mkIdent $ .str tyName str

    let varCtorName ← liftCoreM $ runMetaMAsCoreM $ getVarCtor tyNameGlobal
    let varName ← match varCtorName with
    | some name => pure name
    | none => throwError "ruh roh"
    let varType := (← getConstInfo varName).type
    let var := mkIdent varName

    let from_action := qualify "from_action"
    let from_action_id := qualify "from_action_id"
    let from_action_succ := qualify "from_action_succ"
    let from_action_re := qualify "from_action_re"
    let from_action_su := qualify "from_action_su"
    elabCommand $ ← `(
      @[coe]
      def $from_action : Action $ty → $ty
      | re $y => $var $y
      | su $t => $t

      @[simp, grind =]
      theorem $from_action_id {$n} : $from_action (𝐬0.act $n) = $var $n := by
        simp [$from_action:ident]

      @[simp, grind =]
      theorem $from_action_succ {$n} : $from_action (𝐬1.act $n) = $var ($n + 1) := by
        simp [$from_action:ident]

      @[simp, grind =]
      theorem $from_action_re {$n} : $from_action (re $n) = $var $n := by
        simp [$from_action:ident]

      @[simp, grind =]
      theorem $from_action_su {$n} : $from_action (su $n) = $n := by
        simp [$from_action:ident]

      instance : Coe (Action $ty) $ty where
        coe := $from_action
    )

    -- rmap
    let getLiftsOfTy (data : ArgData) (xs : List Ident) (ty : Ident)  : CommandElabM $ Term := do
      let closure := getClosureFromArgData ty data
      if let some closure := closure then
        let closureTypeExpr ← liftTermElabM $ inferType (← liftTermElabM $ Term.elabTerm closure none)
        if closureTypeExpr.isForall || closureTypeExpr.isArrow then -- does .isForall subsume .isArrow?
          let closureApp ← `(term| $closure $(xs.toArray)*)
          let closureAppExpr ← liftTermElabM $ Term.elabTerm closureApp none
          let closureAppExprReduced ← liftCoreM $ runMetaMAsCoreM $ reduce closureAppExpr
          liftTermElabM closureAppExprReduced.toSyntax
        else
          pure closure
      else
        pure (Syntax.mkNatLit 0)

    let mkLiftArr (data : ArgData) (xs : List Ident) : CommandElabM $ Option Term :=
      match data with
      | .binder _ => do
        let lifts ← tys.mapM $ getLiftsOfTy data xs
        -- Check if all lifts are syntactically just 0
        if List.all lifts (fun stx ↦ BEq.beq stx $ Syntax.mkNatLit 0) then
          pure none
        else
          pure $ ← `([$lifts.toArray,*])
      | _ => do
        pure none

    let rmap := qualify "rmap"
    let rmap_f useTCSyntax ty' data x xs := match data with
    | .var => `($(r).1.act $x) -- NOTE: assumes that the type being generated is the first type in [tys]
    | _ => do
      let tyExpr ← liftTermElabM $ Term.elabTerm ty none
      if ← liftCoreM $ runMetaMAsCoreM $ isDefEq tyExpr ty' then
        if let some liftArr ← mkLiftArr data xs then
          if useTCSyntax then `(($x)⟨$(r).lift $liftArr⟩) else `($rmap ($(r).lift $liftArr) $x)
        else
          if useTCSyntax then `(($x)⟨$(r),⟩) else `($rmap $r $x)
      else if let some theTy ← List.findM? (fun ty ↦ do pure (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm ty.raw none) ty')) tys then
        let r' ← getTy r tys.toArray theTy
        `(($x)⟨$r'⟩)
      else
        `($x)

    let rmapCases ← mkAllCases (rmap_f false) tyNameGlobal
    elabCommand $ ← `(
      @[simp]
      def $rmap ($r : RenVec [$tys.toArray,*]) : $ty → $ty
      $rmapCases:matchAlt*

      instance : RenMap $ty [$tys.toArray,*] where
        rmap := $rmap
    )

    let rmap_fix := qualify "rmap_fix"
    elabCommand $ ← `(
      @[simp]
      theorem $rmap_fix {$r : RenVec [$tys.toArray,*]} {$t : $ty} : $rmap $r $t = $t⟨$r,⟩ := by simp [RenMap.rmap]
    )

    for ctor in ← liftCoreM $ runMetaMAsCoreM $ getConstructors tyNameGlobal do
      let thmName := qualify s!"rmap_{ctor.components.getLast!}"
      let fRhs := rmap_f false
      let fLhs lhs := `(($lhs)⟨$(r),⟩)
      let eq ← mkCtorEq fLhs fRhs ctor
      let args ← mkCtorArgs ctor
      elabCommand $ ← `(
        @[simp, grind =]
        theorem $thmName {$args.toArray*} {$r : RenVec [$tys.toArray,*]} : $eq := rfl
      )

    for ty' in tys do
      let tyList ← (tys.map (·.raw)).mapM (fun `($ty'') ↦ do
        let ty'Expr ← liftTermElabM $ Term.elabTerm ty' none
        let ty''Expr ← liftTermElabM $ Term.elabTerm ty'' none
        if ← liftCoreM $ runMetaMAsCoreM $ isDefEq ty'Expr ty''Expr then
          `($(r).1)
        else
          `(Ren.id $ty''))
      let tyArr := (tyList.append [← `(.unit)]).toArray
      elabCommand $ ← `(
        instance : RenMap $ty [$ty'] where
          rmap $r:ident :=  $rmap ⟨ $tyArr:term,* ⟩
      )

    -- smap
    let getIncrementsOfTy (lifts : List Term) (ty : Name) : CommandElabM $ List (Ident × Term) := do
      let tysLiftsZip := tysNamesGlobal.zip lifts
      let increments : List (Ident × Term) ←
        tysLiftsZip.mapM
          (fun ⟨ty', lift⟩ ↦ do
            -- Is there a better way to check if two names are equal?
            let ty'_eq_ty ← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm (mkIdent ty') none) (← liftTermElabM $ Term.elabTerm (mkIdent ty) none)
            if ¬ ty'_eq_ty ∧ (← isBoundIn ty' ty) then
              pure ⟨mkIdent ty', lift⟩
            else
              pure ⟨mkIdent ty', Syntax.mkNatLit 0⟩)
      pure $ increments.filter (fun (_, stx) ↦ match stx with | `(0) => false | _ => true)

    let mkMapArr (data : ArgData) (xs : List Ident) : CommandElabM $ Option Term :=
      match data with
      | .binder _ => do
        let lifts ← tys.mapM $ getLiftsOfTy data xs
        let optionLifts := lifts.map (fun stx : Term ↦ if BEq.beq stx $ Syntax.mkNatLit 0 then none else some stx)
        -- Check if all lifts are syntactically just 0
        if optionLifts.all (fun | none => false | some _ => true) then
          pure none
        else
          let incrementsList ← tysNamesGlobal.mapM $ getIncrementsOfTy lifts
          let zipped := incrementsList.zip optionLifts
          let ops : List $ Term ← zipped.mapM (fun ⟨incs, lift⟩ ↦ do
            let incOps ← incs.mapM (fun ⟨ty, inc⟩ ↦
              if BEq.beq inc $ Syntax.mkNatLit 0 then `(Ren.id $ty:ident) else `(Ren.add $ty:ident $inc))
            let anyIncs := incs.tail.any (fun ⟨_, inc⟩ ↦ ¬ (BEq.beq inc $ Syntax.mkNatLit 0))

            let tyTail := tysNamesGlobal.tail.toArray.map mkIdent
            match (anyIncs, lift) with
            | (false, none) => `(.skip)
            | (true, none) => `(.ren [$tyTail,*] ⟨$incOps.tail.toArray,*, .nil⟩)
            | (false, some ℓ) => `(.lift $ℓ)
            | (true, some ℓ) => `(.both [$tyTail,*] ⟨$incOps.tail.toArray,*, .nil⟩ $ℓ)
          )
          pure $ some $ ← ops.foldrM (fun t1 t2 ↦ `($t1 $ $t2)) $ ← `(LeanSubst.SubstVec.MapOps.nil)
      | _ => pure none

    let smap := qualify "smap"
    let smap_f useTCSyntax ty' data x xs := match data with
    | .var => throwError "smap var case"
    | _ => do
      let tyExpr ← liftTermElabM $ Term.elabTerm ty none
      if ← liftCoreM $ runMetaMAsCoreM $ isDefEq tyExpr ty' then
        if let some opsArr ← mkMapArr data xs then
          if useTCSyntax then `(($x)[$(σ).map $opsArr]) else `($smap ($(σ).map $opsArr) $x)
          -- if useTCSyntax then `(($x)[$(σ)]) else `($smap ($(σ)) $x)
        else
          if useTCSyntax then `(($x)[$(σ),]) else `($smap $σ $x)
      else if let some theTy ← List.findM? (fun ty ↦ do pure (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm ty.raw none) ty')) tys then
        let σ' ← getTy σ tys.toArray theTy
        `(($x)[$σ'])
      else
        `($x)
    let smap_fVar xs := `($(σ).1.act $(xs[0]!):ident) -- TODO: At the moment, this doesn't generalize to vars with data
    let smapCases ← mkAllCases (smap_f false) tyNameGlobal (fVar := some smap_fVar)

    -- ERROR IS HERE
    elabCommand $ ← `(
      @[simp]
      def $smap ($σ : SubstVec [$tys.toArray,*]) : $ty → $ty
      $smapCases:matchAlt*

      instance : SubstMap $ty [$tys.toArray,*] where
        smap := $smap
    )

  def genAllTys : List Ident → CommandElabM Unit
  | [] => pure ()
  | .cons ty tys => do
    genAllTys tys
    genTy (ty :: tys)

  elab "#leansubst" &"generate" tys:ident,* : command =>
    -- dbg_trace s!"{tys.getElems.toList}"
    genAllTys tys.getElems.toList.reverse

  elab "#leansubst_autogen" ty:ident : command => do
    -- Setup --
    let tyName := ty.raw.getId
    let tyStr := tyName.toString
    let tyNameGlobal ← Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw

  --   let isDefEqTy ty' := liftCoreM $ runMetaMAsCoreM $ isDefEqGuarded ty' (.const tyNameGlobal [])

  --   let qualify str := mkIdent $ .str tyName str
  --   let pairWithTypes names : CommandElabM (List (Ident × Expr)) :=
  --     List.mapM
  --       (fun name => do pure ⟨name, (← getConstInfo name.getId).type⟩)
  --       names

  --   let pairWithTypes' namesAndParams : CommandElabM (List (Ident × Expr × Nat)) :=
  --     List.mapM
  --       (fun ⟨name, i⟩ => do pure ⟨name, (← getConstInfo name.getId).type, i⟩)
  --       namesAndParams


  --   let xN (n : Nat) : TSyntax `term := mkIdent (.mkStr1 $ s!"x{n}")
  --   let xN' (n : Nat) : TSyntax `ident := mkIdent (.mkStr1 $ s!"x{n}")
  --   let x := mkIdent `x
  --   let z := mkIdent `z
  --   let r := mkIdent `r
  --   let n := mkIdent `n
  --   let t := mkIdent `t
  --   let σ := mkIdent `σ
  --   let τ := mkIdent `τ

  --   let identToTerm : Ident → CommandElabM (TSyntax `term) := fun x ↦ `($x:ident)

  --   let varCtorNames ← liftCoreM $ runMetaMAsCoreM $ getVarCtors tyNameGlobal
  --   let varName := varCtorNames[0]!
  --   let varType := (← getConstInfo varName).type
  --   let var := mkIdent varName

  --   let binderCtorNamesWithParams ← liftCoreM $ runMetaMAsCoreM $ getBinderCtors tyNameGlobal
  --   let binderCtorsWithParams : List (Ident × Nat) := binderCtorNamesWithParams.map (fun ⟨name, i⟩ ↦ ⟨mkIdent name, i⟩)
  --   let binderCtorsWithTypesAndParams ← pairWithTypes' binderCtorsWithParams

  --   let nonTaggedCtorNames ← liftCoreM $ runMetaMAsCoreM $ getNonTaggedCtors tyNameGlobal
  --   let nonTaggedCtors := nonTaggedCtorNames.map mkIdent
  --   let nonTaggedCtorsWithTypes ← pairWithTypes nonTaggedCtors

  --   let doVarComputation
  --     : (ty : Type) → ((ctor : Ident) → (varArg : Ident) → (otherArgs : List (Ident × Expr)) → CommandElabM ty)
  --       → CommandElabM ty := fun _ f ↦ do
  --     let argTypes := getForallBinderTypes varType
  --     let argIdents := (List.range $ argTypes.length).map xN'
  --     let argIdentsWithTypes := argIdents.zip argTypes
  --     if let some ⟨argIdent_hd, _⟩ := argIdentsWithTypes.head? then
  --       f var argIdent_hd (argIdents.tail.zip argTypes.tail)
  --     else
  --       throwAbortCommand -- TODO: better error?

  --   let doNonTaggedComputation
  --     : (ty : Type) → ((ctor : Ident) → (args : List (Ident × Expr)) → CommandElabM ty)
  --       → CommandElabM (List ty) := fun _ f ↦ do
  --     nonTaggedCtorsWithTypes.mapM (fun ⟨ctor, type⟩ ↦ do
  --       let argTypes := getForallBinderTypes type
  --       let argIdents := (List.range $ argTypes.length).map xN'
  --       f ctor $ argIdents.zip argTypes
  --     )

  --   let doBinderComputation
  --     : (ty : Type)
  --       → ((ctor : Ident) → (binderArgWithType : Ident × Expr) → (otherArgs : List (Ident × Expr)) → (binderPos : Nat) → CommandElabM ty)
  --       → CommandElabM (List ty) := fun _ f ↦ do
  --     binderCtorsWithTypesAndParams.mapM (fun ⟨ctor, type, i⟩ ↦ do
  --       let argTypes := getForallBinderTypes type
  --       let argIdents := (List.range $ argTypes.length).map xN'
  --       let argIdentsWithTypes := argIdents.zip argTypes
  --       if let some ⟨argIdent_hd, argType_hd⟩ := argIdentsWithTypes.head? then
  --         f ctor ⟨argIdent_hd, argType_hd⟩ (argIdents.tail.zip argTypes.tail) i
  --       else
  --         throwAbortCommand -- TODO: better error?
  --     )

  --   let mkBinderStx
  --     (ctor : Ident) (binderArg : TSyntax `term) (otherArgs : List $ TSyntax `term) (i : Nat) : CommandElabM $ TSyntax `term := do
  --     let beforeBinderArgs := (otherArgs.take i).toArray
  --     let afterBinderArgs := (otherArgs.drop i).toArray
  --     `($ctor $beforeBinderArgs* $binderArg $afterBinderArgs*)

  --   let mkBinderStx'
  --     (ctor : Ident) (binderArg : TSyntax `term) (otherArgs : List $ TSyntax `ident) (i : Nat) : CommandElabM $ TSyntax `term := do
  --     let beforeBinderArgs := (otherArgs.take i).toArray
  --     let afterBinderArgs := (otherArgs.drop i).toArray
  --     `($ctor $beforeBinderArgs* $binderArg $afterBinderArgs*)

  --   let mkBinderArgs
  --     (ty : Name) (binderArg : TSyntax ty) (otherArgs : List $ TSyntax ty) (i : Nat) : TSyntaxArray ty :=
  --     let beforeBinderArgs := (otherArgs.take i).toArray
  --     let afterBinderArgs := (otherArgs.drop i).toArray
  --     beforeBinderArgs ++ [binderArg] ++ afterBinderArgs

  --   -- from_action --
  --   let from_action := qualify "from_action"
  --   elabCommand $ ← `(
  --     @[coe]
  --     def $from_action : Action $ty → $ty
  --     | re y => $var y
  --     | su t => t
  --   )

  --   let from_action_id := qualify "from_action_id"
  --   elabCommand $ ← `(
  --     @[simp, grind =]
  --     theorem $from_action_id {$n} : $from_action (+0σ.act $n) = $var $n := by
  --       simp [$from_action:ident]
  --   )

  --   let from_action_succ := qualify "from_action_succ"
  --   elabCommand $ ← `(
  --     @[simp, grind =]
  --     theorem $from_action_succ {$n} : $from_action (+1σ.act $n) = $var ($n + 1) := by
  --       simp [$from_action:ident]
  --   )

  --   let from_action_re := qualify "from_action_re"
  --   elabCommand $ ← `(
  --     @[simp, grind =]
  --     theorem $from_action_re {$n} : $from_action (re $n) = $var $n := by
  --       simp [$from_action:ident]
  --   )

  --   let from_action_su := qualify "from_action_su"
  --   elabCommand $ ← `(
  --     @[simp, grind =]
  --     theorem $from_action_su {$t} : $from_action (su $t) = $t := by
  --       simp [$from_action:ident]
  --   )

  --   -- Coe --
  --   let instCoe_SubstActionTy_Ty := mkIdent $ .mkStr1 s!"instCoe_SubstAction{tyStr}_{tyStr}"
  --   elabCommand $ ← `(
  --     instance $instCoe_SubstActionTy_Ty:ident : Coe (Action $ty) $ty where
  --       coe := $from_action
  --   )

  --   -- rmap and smap --
  --   let doMapStuff : MapType → CommandElabM Unit :=
  --     fun mapType ↦ do
  --       let leanSubstQualify s := .mkStr2 "LeanSubst" s
  --       let ⟨defIdent, typeIdent, instanceIdent, instanceFieldIdent, rσ, thmPfxStr⟩ : Ident × Ident × Ident × Ident × Ident × String :=
  --         match mapType with
  --         | .is_rmap =>
  --           ⟨qualify "rmap", mkIdent $ leanSubstQualify "Ren", mkIdent $ leanSubstQualify "RenMap", mkIdent $ .mkStr1 "rmap", r, "ren"⟩
  --         | .is_smap =>
  --           ⟨qualify "smap", mkIdent $ leanSubstQualify "Subst", mkIdent $ leanSubstQualify "SubstMap", mkIdent $ .mkStr1 "smap", σ, "subst"⟩

  --       let nonTaggedCases := List.toArray $ ← doNonTaggedComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor args ↦ do
  --         let rhs : List (TSyntax `term) ←
  --           List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($defIdent $rσ $t) else `($t)) args
  --         `(Parser.Term.matchAltExpr| | $ctor $((args.map Prod.fst).toArray)* => $ctor $(rhs.toArray)*)
  --       )

  --       let binderCases := List.toArray $ ← doBinderComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor ⟨binderIdent, _⟩ otherArgs i ↦ do
  --         let otherArgs := mapFst otherArgs
  --         let lhs ← mkBinderStx' ctor binderIdent otherArgs i
  --         let binderRhs ← `($defIdent $(rσ).lift $binderIdent)
  --         let rhs ← mkBinderStx' ctor binderRhs otherArgs i
  --         `(Parser.Term.matchAltExpr| | $lhs => $rhs)
  --       )

  --       let varCase := ← doVarComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor varIdent otherArgs ↦ do
  --         let lhs := List.cons varIdent (otherArgs.map Prod.fst)
  --         let rhsVar ← `($(rσ).act $varIdent)
  --         let rhsOther := otherArgs.tail.map Prod.fst
  --         let rhs := List.cons rhsVar $ ← rhsOther.mapM identToTerm
  --         match mapType with
  --         | .is_rmap => `(Parser.Term.matchAltExpr| | $ctor $(lhs.toArray)* => $ctor $(rhs.toArray)*)
  --         | .is_smap => `(Parser.Term.matchAltExpr| | $ctor $(lhs.toArray)* => $rhsVar)
  --       )

  --       elabCommand $ ← `(
  --         @[simp]
  --         def $defIdent ($rσ : $typeIdent:ident $ty) : $ty → $ty
  --           $varCase:matchAlt
  --           $[$nonTaggedCases:matchAlt]*
  --           $[$binderCases:matchAlt]*
  --       )

  --       let simpCall ← match mapType with
  --       | .is_rmap => `(tactic| simp [RenMap.rmap])
  --       | .is_smap => `(tactic| simp [SubstMap.smap])

  --       elabCommand $ ← `(
  --         instance : $instanceIdent:ident ($ty:ident) ($ty:ident) where
  --           $instanceFieldIdent:ident := $defIdent
  --       )

  --       _ ← doNonTaggedComputation Unit (fun ctor args ↦ do
  --         let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"

  --         let lhsArgs := mapFst args
  --         let lhs ← match mapType with
  --         | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
  --         | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

  --         let rhsArgs ← match mapType with
  --         | .is_rmap => List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($t⟨$rσ⟩) else `($t)) args
  --         | .is_smap => List.mapM (fun ⟨t, ty⟩ ↦ do if ← isDefEqTy ty then `($t[$rσ]) else `($t)) args
  --         let rhs ← `($ctor $(rhsArgs.toArray)*)

  --         elabCommand $ ← `(
  --           @[simp, grind =]
  --           theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
  --             $simpCall:tactic
  --         )
  --       )

  --       _ ← doBinderComputation Unit (fun ctor ⟨binderArg, _⟩ otherArgs i ↦ do
  --         let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"
  --         let otherArgs := mapFst otherArgs

  --         let lhsArgs := mkBinderArgs `ident binderArg otherArgs i
  --         let lhs ← match mapType with
  --         | .is_rmap => `(($ctor $lhsArgs*)⟨$rσ⟩)
  --         | .is_smap => `(($ctor $lhsArgs*)[$rσ])

  --         let rhsBinder ← match mapType with
  --         | .is_rmap => `($binderArg⟨$(rσ).lift⟩)
  --         | .is_smap => `($binderArg[$(rσ).lift])
  --         let rhs ← mkBinderStx' ctor rhsBinder otherArgs i

  --         elabCommand $ ← `(
  --           @[simp, grind =]
  --           theorem $thmName {$lhsArgs*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
  --             $simpCall:tactic
  --         )
  --       )

  --       _ ← doVarComputation Unit (fun ctor varArg otherArgs ↦ do
  --         let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"
  --         let lhsArgs := varArg :: mapFst otherArgs
  --         let lhs ← match mapType with
  --         | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
  --         | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

  --         let rhsVar ← `($(rσ).act $varArg)
  --         let rhsOther ← List.mapM (fun ⟨t, _⟩ ↦ `($t)) otherArgs
  --         let rhsArgs := rhsVar :: rhsOther
  --         let rhs ← match mapType with
  --         | .is_rmap => `($ctor $(rhsArgs.toArray)*)
  --         | .is_smap => pure rhsVar

  --         elabCommand $ ← `(
  --           @[simp, grind =]
  --           theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
  --             $simpCall:tactic
  --         )
  --       )

  --   doMapStuff .is_rmap
  --   doMapStuff .is_smap

  --   -- from_action --
  --   let from_action_compose := qualify "from_action_compose"
  --   let from_action_compose_ren := qualify "from_action_compose_ren"
  --   elabCommand $ ← `(
  --     @[simp]
  --     theorem $from_action_compose {$x : Nat} {$σ $τ : Subst $ty}
  --       : ($from_action (Subst.act $σ $x))[$τ] = $from_action (($σ ∘ $τ).act $x)
  --     := by
  --       simp [$from_action:ident, Subst.compose]
  --       generalize zdef : $(σ).act $x = $z
  --       cases $z:ident <;> simp [$from_action:ident]

  --     @[simp]
  --     theorem $from_action_compose_ren {$x : Nat} {$σ : Subst $ty} {$r : Ren $ty}
  --       : ($from_action:ident ($(σ).act $x))⟨$r⟩ = $from_action:ident (($σ ∘ $r).act $x)
  --     := by
  --       simp [$from_action:ident]
  --       generalize zdef : $(σ).act $x = $z
  --       cases $z:ident <;> simp
  --   )

  --   -- instances --
  --   elabCommand $ ← `(
  --     instance : RenMapId $ty $ty where
  --       apply_id := by subst_solve_id

  --     instance : RenMapCompose $ty $ty where
  --       apply_compose := by subst_solve_compose

  --     instance : SubstMapId $ty $ty where
  --       apply_id := by subst_solve_id

  --     instance : SubstMapStable $ty $ty where
  --       apply_stable := by subst_solve_stable

  --     instance : SubstMapRenComposeLeft $ty $ty where
  --       apply_ren_compose_left := by subst_solve_compose

  --     instance : SubstMapRenComposeRight $ty $ty where
  --       apply_ren_compose_right := by subst_solve_compose

  --     instance : SubstMapCompose $ty $ty where
  --       apply_compose := by subst_solve_compose
  --   )

end Automation
