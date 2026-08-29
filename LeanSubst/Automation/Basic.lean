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
  def s := mkIdent `s
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
    for _ in List.range $ pos do
      stx ← `($stx.2)
    `($stx.1)

  def forEachSuffix : (tys : List Ident) → (f : List Ident → CommandElabM Unit) → CommandElabM Unit
  | [], _ => pure ()
  | tys@(.cons _ tys'), f => do
    f tys
    forEachSuffix tys' f

  def forEachPrefix : (tys : List Ident) → (f : List Ident → CommandElabM Unit) → CommandElabM Unit
  | [], _ => pure ()
  | tys@(.cons _ _), f => do
    f tys
    forEachSuffix tys.reverse.tail.reverse f

  def forHeadAndEachSuffix : (tys : List Ident) → (f : List Ident → CommandElabM Unit) → CommandElabM Unit
  | [], _ => pure ()
  | .cons ty [], f => do f [ty]
  | tys@(.cons ty _), f => do
    f [ty]
    forEachSuffix tys f

  def forEachCtor (ty : Name) (f : Name → CommandElabM Unit) : CommandElabM Unit := do
    for ctor in ← liftCoreM $ runMetaMAsCoreM $ getConstructors ty do f ctor

  inductive MapOrLift
  | map : Term → MapOrLift
  | lift : Term → MapOrLift
  | none : MapOrLift

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
      theorem $from_action_id {$n} : $from_action (𝐬0.act $n) = $var $n := rfl

      @[simp, grind =]
      theorem $from_action_succ {$n} : $from_action (𝐬1.act $n) = $var ($n + 1) := rfl

      @[simp, grind =]
      theorem $from_action_re {$n} : $from_action (re $n) = $var $n := rfl

      @[simp, grind =]
      theorem $from_action_su {$n} : $from_action (su $n) = $n := rfl

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
          if useTCSyntax then `(($x)⟨$(r).lift $liftArr,⟩) else `($rmap ($(r).lift $liftArr) $x)
        else
          if useTCSyntax then `(($x)⟨$(r),⟩) else `($rmap $r $x)
      else if let some theTy ← List.findM? (fun ty ↦ do pure (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm ty.raw none) ty')) tys then
        let r' ← getTy r tys.toArray theTy
        dbg_trace s!"\nVAR {x} with type {ty'} and rmap {r'}\n"
        `(($x⟨$r'⟩))
      else
        `($x)

    let rmapCases ← mkAllCases (rmap_f false) tyNameGlobal
    elabCommand $ ← `(
      @[simp]
      def $rmap ($r : RenVec [$tys.toArray,*]) : $ty → $ty
      $rmapCases:matchAlt*

      instance : RenMap $ty [$tys.toArray,*] where
        rmap := $rmap

      instance : RenMap $ty [] where
        rmap _ := id
    )

    -- If the length of `tys` is 1, then we've already done the only necessary RenMap
    -- TODO: check, do we also need all prefixes here?
    if tys.length > 1 then
      for ty' in tys do
        let tyList ← (tys.map (·.raw)).mapM (fun `($ty'') ↦ do
          let ty'Expr ← liftTermElabM $ Term.elabTerm ty' none
          let ty''Expr ← liftTermElabM $ Term.elabTerm ty'' none
          if ← liftCoreM $ runMetaMAsCoreM $ isDefEq ty'Expr ty''Expr then
            `($(r).1)
          else
            `(Ren.id $ty''))
        let tyArr := (tyList.append [← `(.nil)]).toArray
        dbg_trace s!"INSTANCE {ty} ⟨{ty'}⟩\n\n"
        elabCommand $ ← `(
          instance : RenMap $ty [$ty'] where
            rmap $r:ident :=  $rmap ⟨ $tyArr:term,* ⟩
        )

    -- TODO: do we also need suffixes?
    forEachPrefix tys (fun tys ↦ do
      let head := tys.head!
      let tail := tys.tail
      dbg_trace s!"SUFFIX --- head: {head}, tail: {tail}"
      elabCommand $ ← `(
        instance : RenSuffix $head:ident [$tail.toArray,*] := ⟨⟩
      )
    )

    let rmap_fix := qualify "rmap_fix"
    elabCommand $ ← `(
      @[simp]
      theorem $rmap_fix {$r : RenVec [$tys.toArray,*]} {$t : $ty} : $rmap $r $t = $t⟨$r,⟩ := by simp [RenMap.rmap]
    )

    let rmap_empty := qualify "rmap_empty"
    elabCommand $ ← `(
      @[simp]
      theorem $rmap_empty {$t : $ty} {$r : RenVec []} : $t⟨$r,⟩ = $t := rfl
    )

    forHeadAndEachSuffix tys (fun pfx ↦ forEachCtor tyNameGlobal (fun ctor ↦ do
      let tyQual := if tys.length = 1 then "" else "_" ++ ("_".intercalate $ pfx.map (fun ty ↦ ty.raw.getId.toString.toLower))
      let thmName := qualify s!"rmap{tyQual}_{ctor.components.getLast!}"
      dbg_trace s!"NAME: {thmName}"
      let fRhs := rmap_f true
      let fLhs lhs := `(($lhs)⟨$(r),⟩)
      -- TODO: Ah fuck we actually have to be careful here. The ".2.1" depends on which variant we're making.
      let eq ← mkCtorEq fLhs fRhs ctor
      let args ← mkCtorArgs ctor
      elabCommand $ ← `(
        @[simp]
        theorem $thmName {$args.toArray*} {$r : RenVec [$pfx.toArray,*]} : $eq := rfl
      )
    ))

    let from_action_rmap := qualify "from_action_rmap"
    elabCommand $ ← `(
      @[simp]
      theorem $from_action_rmap {$t : Action $ty} {$r : RenVec [$tys.toArray,*]} : ($from_action $t)⟨$r,⟩ = $from_action ($t⟨$r,⟩) := by
        cases $t:ident <;> simp [$from_action:ident]
    )

    elabCommand $ ← `(
      instance : RenMapEmpty $ty where
        apply_empty := by intro $s:ident; simp [RenMap.rmap]

      instance : RenMapId $ty [$ty] where
        apply_id := by subst_solve_id

      instance : RenMapCompose $ty [$ty] where
        apply_compose := by subst_solve_compose
    )

    let instRenMapAll_ty := mkIdent $ .mkStr1 s!"instRenMapAll_{ty.raw.getId.toString}" -- not qualified
    elabCommand $ ← `(
      @[reducible, simp]
      instance $instRenMapAll_ty:ident : RenMapAll [$ty] := .cons .nil
    )
    if tys.length > 1 then
      let tysPostfix := "_".intercalate (tys.map (·.raw.getId.toString))
      let tysPostfix' := "_".intercalate (tys.tail.map (·.raw.getId.toString))
      let instRenMapAll_tys := mkIdent $ .mkStr1 s!"instRenMapAll_{tysPostfix}" -- not qualified
      let instRenMapAll_tys' := mkIdent $ .mkStr1 s!"instRenMapAll_{tysPostfix'}" -- not qualified
      elabCommand $ ← `(
        instance $instRenMapAll_tys:ident : RenMapAll [$tys.toArray:ident,*] := .cons $instRenMapAll_tys'
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

    let mkMapArr (data : ArgData) (xs : List Ident) : CommandElabM $ Option MapOrLift :=
      match data with
      | .binder blah => do
        let lifts ← tys.mapM $ getLiftsOfTy data xs
        let optionLifts := lifts.map (fun stx : Term ↦ if BEq.beq stx $ Syntax.mkNatLit 0 then none else some stx)
        dbg_trace s!"\nLIFTS: {optionLifts} for data {blah}\n"

        -- Check if all lifts are syntactically just 0
        if optionLifts.all (fun | none => true | some _ => false) then
          pure none
        else
          let incrementsList ← tysNamesGlobal.mapM $ getIncrementsOfTy lifts
          let zipped := incrementsList.zip optionLifts
          let ops : List $ Term × Bool ← zipped.mapM (fun ⟨incs, lift⟩ ↦ do
            let incOps ← incs.mapM (fun ⟨ty, inc⟩ ↦
              if BEq.beq inc $ Syntax.mkNatLit 0 then `(Ren.id $ty:ident) else `(Ren.add $ty:ident $inc))
            let anyIncs := incs.tail.any (fun ⟨_, inc⟩ ↦ ¬ (BEq.beq inc $ Syntax.mkNatLit 0))

            let tyTail := tysNamesGlobal.tail.toArray.map mkIdent
            dbg_trace s!"MATCHING on {(anyIncs, lift)}"
            let op ← match (anyIncs, lift) with
            | (false, none) => `(.skip)
            | (true, none) => `(.ren [$tyTail,*] ⟨$incOps.tail.toArray,*, .nil⟩)
            | (false, some ℓ) => `(.lift $ℓ)
            | (true, some ℓ) => `(.both [$tyTail,*] ⟨$incOps.tail.toArray,*, .nil⟩ $ℓ)
            pure ⟨op, anyIncs⟩
          )
          if ops.all (¬ ·.2) then -- If we don't have to apply any renamings
            pure $ MapOrLift.lift $ ← `([$lifts.toArray,*])
          else
            pure $ MapOrLift.map $ ← (ops.map Prod.fst).foldrM (fun t1 t2 ↦ `($t1 $ $t2)) $ ← `(LeanSubst.SubstVec.MapOps.nil)
      | _ => pure none

    let smap := qualify "smap"
    let smap_f useTCSyntax ty' data x xs := match data with
    | .var => throwError "smap var case"
    | _ => do
      let tyExpr ← liftTermElabM $ Term.elabTerm ty none
      if ← liftCoreM $ runMetaMAsCoreM $ isDefEq tyExpr ty' then
        if let MapOrLift.map opsArr ← mkMapArr data xs then
          if useTCSyntax then `(($x)[$(σ).map $opsArr]) else `($smap ($(σ).map $opsArr) $x)
        else if let MapOrLift.lift opsArr ← mkMapArr data xs then
          if useTCSyntax then `(($x)[$(σ).lift $opsArr]) else `($smap ($(σ).lift $opsArr) $x)
        else
          if useTCSyntax then `(($x)[$(σ),]) else `($smap $σ $x)
      else if let some theTy ← List.findM? (fun ty ↦ do pure (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm ty.raw none) ty')) tys then
        let σ' ← getTy σ tys.toArray theTy
        `(($x)[$σ'])
      else
        `($x)
    let smap_fVar xs := `($(σ).1.act $(xs[0]!):ident) -- TODO: At the moment, this doesn't generalize to vars with data
    let smapCases ← mkAllCases (smap_f false) tyNameGlobal (fVar := some smap_fVar)

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

end Automation
