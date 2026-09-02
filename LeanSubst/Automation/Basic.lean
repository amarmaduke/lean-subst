import LeanSubst
import Lean.Elab.Tactic
import Lean.Elab.Term.TermElabM
import LeanSubst.Automation.Attributes

namespace Automation
  open Lean Elab Elab.Term Tactic Meta LeanSubst Command LeanSubstAttributes

  @[inline]
  def runMetaMAsCoreM {α : Type} (x : MetaM α) : CoreM α := Prod.fst <$> x.run {} {}

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

  -- We use this to get the types of all the arguments in a constructor
  def getForallBinderTypes : Expr → List Expr
  | .forallE _ t b _ => t :: getForallBinderTypes b
  | _ => []

  -- A lot of the metaprogramming stuff is replicated between rmap and smap, with minor changes here and there.
  -- Therefore, we often write functions that take a MapType as a flag argument and produce the definition, theorem, etc.
  inductive MapType
  | rmap
  | smap

  -- Names of variables
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

  -- For each constructor argument in which something is bound, we need to keep track of how many of each thing is bound.
  inductive ArgData
  | binder : List (Term × Ident) → ArgData -- (Term × Ident) corresponds to ([num bound closure] × [type being bound])
  | var
  | none

  -- The "closure" is a function that takes the arguments of the constructor and returns the number of bound variables.
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

  -- Applies f to each argument
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

  def mkVarCtorRhs (f : List Ident → Term → CommandElabM Term) (ctor : Name) : CommandElabM $ Term := do
    f (← mkCtorArgs ctor) $ mkIdent ctor

  def mkVarCtorCase (f : List Ident → Term → CommandElabM Term) (ctor : Name) : CommandElabM $ TSyntax `Lean.Parser.Term.matchAltExpr := do
    let lhs ← mkCtorLhs ctor
    let rhs ← mkVarCtorRhs f ctor
    `(Parser.Term.matchAltExpr| | $lhs => $rhs)

  def mkCtorEq (fLhs : Term → CommandElabM Term) (fRhs : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ctor : Name) (fVar : Option (List Ident → Term → CommandElabM Term) := none): CommandElabM $ Term := do
    let lhs ← mkCtorLhs ctor >>= fLhs
    let rhs ←
      if ← liftCoreM $ runMetaMAsCoreM $ isVar ctor then
        if let some fVar := fVar then mkVarCtorRhs fVar ctor else mkCtorRhs fRhs ctor
      else
        mkCtorRhs fRhs ctor
    `($lhs = $rhs)

  -- We need to give the option of handling the var case by doing more than just mapping each argument, hence the fVar argument here.
  def mkAllCases (f : Expr → ArgData → Ident → List Ident → CommandElabM Term) (ty : Name) (fVar : Option (List Ident → Term → CommandElabM Term) := none) : CommandElabM $ TSyntaxArray `Lean.Parser.Term.matchAltExpr := do
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

  -- Given an RenVec or SubstVec, extracts the correctly-typed entry.
  def getTy (rσ : Ident) (tys : Array Ident) (ty : Ident) : CommandElabM Term := do
    let pos := tys.idxOf ty
    let mut stx ← `($rσ)
    for _ in List.range $ pos do
      stx ← `($stx.2)
    `($stx.1)

  -- Applies a computation for each suffix in the list Tys.
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

  def forEachTy (tys : List Ident) (f : Ident → CommandElabM Unit) : CommandElabM Unit := do
    for ty in tys do f ty

  -- We use this as a return value to indicate whether the returned term should be applied as a map or as a lift.
  inductive MapOrLift
  | map : Term → MapOrLift
  | lift : Term → MapOrLift
  | none : MapOrLift

  -- The main function
  def genTy (tys : List Ident) : CommandElabM Unit := do
    let toGlobal (ty : Ident) : CommandElabM Name := Command.liftCoreM $ realizeGlobalConstNoOverload ty.raw
    let ty := tys[0]!
    let tyName := ty.raw.getId
    let tyStr := tyName.toString
    let tyNameGlobal ← toGlobal ty

    dbg_trace s!"Generating {ty} with list {tys}"

    let tyArr ← `([$tys.toArray,*])
    let tysNamesGlobal ← tys.mapM toGlobal

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


    let rmap := qualify "rmap"
    let smap := qualify "smap"

    let mkMapSingletonInstance (mapType : MapType) (ty' : Ident) := do
      let tyList ← (tys.map (TSyntax.raw ·)).mapM (fun `($ty'') ↦ do
        let ty'Expr ← liftTermElabM $ Term.elabTerm ty' none
        let ty''Expr ← liftTermElabM $ Term.elabTerm ty'' none
        if ← liftCoreM $ runMetaMAsCoreM $ isDefEq ty'Expr ty''Expr then
          match mapType with | .rmap => `($(r).1) | .smap => `($(σ).1)
        else
          match mapType with | .rmap => `(Ren.id $ty'') | .smap => `(Subst.id $ty''))
      let tyArr := (tyList.append [← `(.nil)]).toArray
      match mapType with
      | .rmap =>
        elabCommand $ ← `(
          instance : RenMap $ty [$ty'] where
            rmap $r:ident := $rmap ⟨ $tyArr:term,* ⟩
        )
      | .smap =>
        elabCommand $ ← `(
          instance : SubstMap $ty [$ty'] where
            smap $σ:ident := $smap ⟨ $tyArr:term,* ⟩
        )

    let mkMapInstances (mapType : MapType) := do
      match mapType with
      | .rmap =>
        elabCommand $ ← `(
          instance : RenMap $ty [$tys.toArray,*] where
            rmap := $rmap

          instance : RenMap $ty [] where
            rmap _ := id
        )
      | .smap =>
        elabCommand $ ← `(
          instance : SubstMap $ty [$tys.toArray,*] where
            smap := $smap

          instance : SubstMap $ty [] where
            smap _ := id
        )
      -- If the length of `tys` is 1, then we've already done the only necessary RenMap
      -- TODO: check, do we also need all prefixes here?
      if tys.length > 1 then
        forEachTy tys $ mkMapSingletonInstance mapType

    let mkSuffixInstances (mapType : MapType) := do
      let TheSuffix ← match mapType with | .rmap => ``(RenSuffix) | .smap => ``(SubstSuffix)
      forEachSuffix tys.tail (fun sfx ↦ do
        elabCommand $ ← `(
          instance : $TheSuffix $ty:ident [$sfx.toArray,*] := ⟨⟩
        )
      )
      elabCommand $ ← `(
        instance : $TheSuffix $ty:ident [] := ⟨⟩
      )

    -- rmap setup
    let getLiftsOfTy (data : ArgData) (xs : List Ident) (ty : Ident)  : CommandElabM $ Term := do
      let closure := getClosureFromArgData ty data
      if let some closure := closure then
        let closureTypeExpr ← liftTermElabM $ inferType (← liftTermElabM $ Term.elabTerm closure none)
        if closureTypeExpr.isForall || closureTypeExpr.isArrow then -- does .isForall subsume .isArrow?
          let closureApp ← `(term| $closure $(xs.toArray)*)
          let closureAppExpr ← liftTermElabM $ Term.elabTerm closureApp none
          let closureAppExprReduced ← liftCoreM $ runMetaMAsCoreM $ reduce closureAppExpr
          liftTermElabM (exprToSyntax closureAppExprReduced)
        else
          pure closure
      else
        pure (Syntax.mkNatLit 0)

    let mkLiftArr (data : ArgData) (xs : List Ident) (tys := tys) : CommandElabM $ Option Term :=
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

    -- smap setup
    let getIncrementsOfTy (lifts : List Term) (tysNamesGlobal : List Name) (ty : Name) : CommandElabM $ List (Ident × Term) := do
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

    let mkMapArr (data : ArgData) (xs : List Ident) (tys : List Ident) : CommandElabM $ Option MapOrLift :=
      match data with
      | .binder _ => do
        let lifts ← tys.mapM $ getLiftsOfTy data xs
        let optionLifts := lifts.map (fun stx : Term ↦ if BEq.beq stx $ Syntax.mkNatLit 0 then none else some stx)
        -- Check if all lifts are syntactically just 0
        if optionLifts.all (fun | none => true | some _ => false) then
          pure none
        else
          let tysNamesGlobal ← tys.mapM toGlobal
          let incrementsList ← tysNamesGlobal.mapM $ getIncrementsOfTy lifts tysNamesGlobal
          let zipped := incrementsList.zip optionLifts
          let ops : List $ Term × Bool ← zipped.mapM (fun ⟨incs, lift⟩ ↦ do
            let incOps ← incs.mapM (fun ⟨ty, inc⟩ ↦
              if BEq.beq inc $ Syntax.mkNatLit 0 then `(Ren.id $ty:ident) else `(Ren.add $ty:ident $inc))
            let anyIncs := incs.tail.any (fun ⟨_, inc⟩ ↦ ¬ (BEq.beq inc $ Syntax.mkNatLit 0))

            let tyTail := tysNamesGlobal.tail.toArray.map mkIdent
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

    let smap_fVar (tys : List Ident) xs ctor : CommandElabM Term := do
      if (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm tys[0]!.raw none) (← liftTermElabM $ Term.elabTerm ty.raw none)) then
        `($(σ).1.act $(xs[0]!):ident) -- TODO: At the moment, this doesn't generalize to vars with data
      else
        `($ctor $(xs[0]!):ident)

    -- rmap/smap arg mapping function
    let map_f (mapType : MapType) (useTCSyntax : Bool) ty' data (x : Ident) (xs : List Ident) (tys := tys) := match data with
    | ArgData.var => do
      match mapType with
      | .rmap =>
        if (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm tys[0]!.raw none) (← liftTermElabM $ Term.elabTerm ty.raw none)) then
          `($(r).1.act $x) -- NOTE: assumes that the type being generated is the first type in [tys]
        else
          `($x)
      | .smap => throwError "smap var case"
    | _ => do
      let tyExpr ← liftTermElabM $ Term.elabTerm ty none
      if ← liftCoreM $ runMetaMAsCoreM $ isDefEq tyExpr ty' then
        match mapType with
        | .rmap =>
          if let some liftArr ← mkLiftArr data xs (tys := tys) then
            if useTCSyntax then `(($x)⟨$(r).lift $liftArr,⟩) else `($rmap ($(r).lift $liftArr) $x)
          else
            if useTCSyntax then `(($x)⟨$(r),⟩) else `($rmap $r $x)
        | .smap =>
          if let MapOrLift.map opsArr ← mkMapArr data xs tys then
            if useTCSyntax then `(($x)[$(σ).map $opsArr,]) else `($smap ($(σ).map $opsArr) $x)
          else if let MapOrLift.lift opsArr ← mkMapArr data xs tys then
            if useTCSyntax then `(($x)[$(σ).lift $opsArr,]) else `($smap ($(σ).lift $opsArr) $x)
          else
            if useTCSyntax then `(($x)[$(σ),]) else `($smap $σ $x)
      else if let some theTy ← List.findM? (fun (ty : Ident) ↦ do pure (← liftCoreM $ runMetaMAsCoreM $ isDefEq (← liftTermElabM $ Term.elabTerm ty.raw none) ty')) tys then
        match mapType with
        | .rmap =>
          let r' ← getTy r tys.toArray theTy
          `(($x⟨$r'⟩))
        | .smap =>
          let σ' ← getTy σ tys.toArray theTy
          `(($x)[$σ'])
      else
        `($x)

    -- theorems
    let mkMapThms (mapType : MapType) := do
      let mapStr := match mapType with | .rmap => "rmap" | .smap => "smap"
      let rσ : Ident := match mapType with | .rmap => r | .smap => σ
      let map := match mapType with | .rmap => rmap | .smap => smap
      let map_fix := qualify s!"{mapStr}_fix"
      let TheVec ← match mapType with | .rmap => ``(RenVec) | .smap => ``(SubstVec)

      let eq ← match mapType with
      | .rmap => `($map $rσ $t = $t⟨$rσ,⟩)
      | .smap => `($map $rσ $t = $t[$rσ,])
      let simp ← match mapType with | .rmap => `(by simp [RenMap.rmap]) | .smap => `(by simp [SubstMap.smap])
      elabCommand $ ← `(
        @[simp]
        theorem $map_fix {$rσ : $TheVec [$tys.toArray,*]} {$t : $ty} : $eq := $simp
      )

      let map_empty := qualify s!"{mapStr}_empty"
      let eq ← match mapType with | .rmap => `($t⟨$rσ,⟩ = $t) | .smap => `($t[$rσ,] = $t)
      elabCommand $ ← `(
        @[simp]
        theorem $map_empty {$t : $ty} {$rσ : $TheVec []} : $eq := rfl
      )

      let proof ← match mapType with
      | .rmap => `(by first | rfl | simp only [RenMap.rmap] ; rw [$rmap:ident] ; try simp | simp only [RenMap.rmap] ; simp)
      | .smap => `(by first | rfl | simp only [SubstMap.smap] ; rw [$smap:ident] ; try simp | simp only [SubstMap.smap] ; simp)
      forHeadAndEachSuffix tys (fun sfx ↦ forEachCtor tyNameGlobal (fun ctor ↦ do
        let tyQual := if tys.length = 1 then "" else "_" ++ ("_".intercalate $ sfx.map (fun (ty : Ident) ↦ ty.raw.getId.toString.toLower))
        let thmName := qualify s!"{mapStr}{tyQual}_{ctor.components.getLast!}"
        let fRhs := map_f mapType true (tys := sfx)
        let fLhs lhs : CommandElabM Term := match mapType with | .rmap => `(($lhs)⟨$(rσ),⟩) | .smap => `(($lhs)[$(rσ),])
        let eq ← mkCtorEq fLhs fRhs ctor (fVar := match mapType with | .rmap => none | .smap => some $ smap_fVar sfx)
        let args ← mkCtorArgs ctor
        elabCommand $ ← `(
          @[simp]
          theorem $thmName {$args.toArray*} {$rσ : $TheVec [$sfx.toArray,*]} : $eq :=
            $proof
        )
      ))

    let mkFromActionMapThms (mapType : MapType) := do
      let map := match mapType with | .rmap => "rmap" | .smap => "smap"
      let from_action_map := qualify s!"from_action_{map}"
      let rσ : Ident := match mapType with | .rmap => r | .smap => σ
      let eq ← match mapType with
      | .rmap => `(($from_action $t)⟨$rσ,⟩ = $from_action ($t⟨$rσ,⟩))
      | .smap => `(($from_action $t)[$rσ,] = $from_action ($t[$rσ,]))
      let TheVec ← match mapType with | .rmap => ``(RenVec) | .smap => ``(SubstVec)
      elabCommand $ ← `(
        @[simp]
        theorem $from_action_map {$t : Action $ty} {$rσ : $TheVec [$tys.toArray,*]} : $eq := by
          cases $t:ident <;> (first | rfl | simp | simp [$from_action:ident])
      )

      let from_action_mapi (i : Nat) := qualify $ s!"from_action_{map}{i}"
      if tys.length > 1 then
        for i in List.range tys.length do
          elabCommand $ ← `(
            @[simp]
            theorem $(from_action_mapi i) {$t : Action $ty} {$rσ : $TheVec [$(tys[i]!)]} : $eq := by
              cases $t:ident <;> (first | rfl | simp | simp [$from_action:ident])
          )

    let mkMapAllInstances (mapType : MapType) := do
      let TheMapStr := match mapType with | .rmap => "RenMap" | .smap => "SubstMap"
      let TheMapAll ← match mapType with | .rmap => ``(LeanSubst.RenMapAll) | .smap => ``(LeanSubst.SubstMapAll)
      let instTheMapAll_ty := mkIdent $ .mkStr1 s!"inst{TheMapStr}All_{ty.raw.getId.toString}" -- not qualified
      elabCommand $ ← `(
        @[reducible, simp]
        instance $instTheMapAll_ty:ident : $TheMapAll [$ty] := .cons .nil
      )
      if tys.length > 1 then
        let tysPostfix := "_".intercalate (tys.map (fun (ty : Ident) ↦ ty.raw.getId.toString))
        let tysPostfix' := "_".intercalate (tys.tail.map (fun (ty : Ident) ↦ ty.raw.getId.toString))
        let instTheMapAll_tys := mkIdent $ .mkStr1 s!"inst{TheMapStr}All_{tysPostfix}" -- not qualified
        let instTheMapAll_tys' := mkIdent $ .mkStr1 s!"inst{TheMapStr}All_{tysPostfix'}" -- not qualified
        elabCommand $ ← `(
          instance $instTheMapAll_tys:ident : $TheMapAll [$tys.toArray:ident,*] := .cons $instTheMapAll_tys'
        )

    -- Executing rmap stuff
    let rmapCases ← mkAllCases (map_f .rmap false) tyNameGlobal
    elabCommand $ ← `(
      @[simp]
      def $rmap ($r : RenVec [$tys.toArray,*]) : $ty → $ty
      $rmapCases:matchAlt*
    )

    mkMapInstances .rmap
    mkSuffixInstances .rmap
    mkMapThms .rmap
    mkFromActionMapThms .rmap

    elabCommand $ ← `(
      instance : RenMapEmpty $ty where
        apply_empty := by intro $s:ident; simp [RenMap.rmap]

      instance : RenMapId $ty [$ty] where
        apply_id := by subst_solve_id

      instance : RenMapCompose $ty [$ty] where
        apply_compose := by subst_solve_compose
    )

    mkMapAllInstances .rmap

    -- Executing smap stuff
    let smapCases ← mkAllCases (map_f .smap false) tyNameGlobal (fVar := some $ smap_fVar tys)

    elabCommand $ ← `(
      @[simp]
      def $smap ($σ : SubstVec [$tys.toArray,*]) : $ty → $ty
      $smapCases:matchAlt*
    )

    mkMapInstances .smap
    mkSuffixInstances .smap
    mkMapAllInstances .smap
    mkMapThms .smap
    mkFromActionMapThms .smap

    elabCommand $ ← `(
      instance : SubstMapEmpty $ty where
        apply_empty := by intro $s:ident; simp [SubstMap.smap]

      instance : SubstMapId $ty [$ty] where
        apply_id := by subst_solve_id

      instance : SubstMapStable $ty [$ty] where
        apply_stable := by subst_solve_stable

      instance : SubstMapRenComposeLeft $ty [$ty] where
        apply_ren_compose_left := by subst_solve_compose

      instance : SubstMapRenComposeRight $ty [$ty] where
        apply_ren_compose_right := by subst_solve_compose

      instance : SubstMapCompose $ty [$ty] where
        apply_compose := by subst_solve_compose
    )

  def genAllTys : List Ident → CommandElabM Unit
  | [] => pure ()
  | .cons ty tys => do
    genAllTys tys
    genTy (ty :: tys)

  elab "#leansubst" &"generate" tys:ident,* : command =>
    genAllTys tys.getElems.toList.reverse

end Automation
