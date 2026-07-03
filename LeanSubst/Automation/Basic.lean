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
    apply_stable := sorry -- by subst_solve_stable

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

    let qualify str := mkIdent $ .str tyName str
    let pairWithTypes names : CommandElabM (List (Ident × Expr)) :=
      List.mapM
        (fun name => do pure ⟨name, (← getConstInfo name.getId).type⟩)
        names

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

    let binderCtorNames ← liftCoreM $ runMetaMAsCoreM $ getBinderCtors tyNameGlobal
    let binderCtors := binderCtorNames.map mkIdent
    let binderCtorsWithTypes ← pairWithTypes binderCtors

    let nonTaggedCtorNames ← liftCoreM $ runMetaMAsCoreM $ getNonTaggedCtors tyNameGlobal
    let nonTaggedCtors := nonTaggedCtorNames.map mkIdent
    let nonTaggedCtorsWithTypes ← pairWithTypes nonTaggedCtors

    let mkVarComputation
      : (ty : Type) → ((ctor : Ident) → (varArg : Ident) → (otherArgs : List (Ident × Expr)) → CommandElabM ty)
        → CommandElabM ty := fun _ f ↦ do
      let argTypes := getForallBinderTypes varType
      let argIdents := (List.range $ argTypes.length).map xN'
      let argIdentsWithTypes := argIdents.zip argTypes
      if let some ⟨argIdent_hd, _⟩ := argIdentsWithTypes.head? then
        f var argIdent_hd (argIdents.tail.zip argTypes.tail)
      else
        throwAbortCommand -- TODO: better error?

    let mkNonTaggedComputation
      : (ty : Type) → ((ctor : Ident) → (args : List (Ident × Expr)) → CommandElabM ty)
        → CommandElabM (List ty) := fun _ f ↦ do
      nonTaggedCtorsWithTypes.mapM (fun ⟨ctor, type⟩ ↦ do
        let argTypes := getForallBinderTypes type
        let argIdents := (List.range $ argTypes.length).map xN'
        f ctor $ argIdents.zip argTypes
      )

    let mkBinderComputation
      : (ty : Type)
        → ((ctor : Ident) → (binderArgWithType : Ident × Expr) → (otherArgs : List (Ident × Expr)) → CommandElabM ty)
        → CommandElabM (List ty) := fun _ f ↦ do
      binderCtorsWithTypes.mapM (fun ⟨ctor, type⟩ ↦ do
        let argTypes := getForallBinderTypes type
        let argIdents := (List.range $ argTypes.length).map xN'
        let argIdentsWithTypes := argIdents.zip argTypes
        if let some ⟨argIdent_hd, argType_hd⟩ := argIdentsWithTypes.head? then
          f ctor ⟨argIdent_hd, argType_hd⟩ (argIdents.tail.zip argTypes.tail)
        else
          throwAbortCommand -- TODO: better error?
      )

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

    let doMapStuff : MapType → CommandElabM Unit :=
      fun mapType ↦ do
        let ⟨defIdent, typeIdent, instanceIdent, instanceFieldIdent, rσ, thmPfxStr⟩ : Ident × Ident × Ident × Ident × Ident × String :=
          match mapType with
          | .is_rmap =>
            ⟨qualify "rmap", mkIdent $ .mkStr1 "Ren", mkIdent $ .mkStr1 "RenMap", mkIdent $ .mkStr1 "rmap", r, "ren"⟩
          | .is_smap =>
            ⟨qualify "smap", mkIdent $ .mkStr1 "Subst", mkIdent $ .mkStr1 "SubstMap", mkIdent $ .mkStr1 "smap", σ, "subst"⟩

        let nonTaggedCases := List.toArray $ ← mkNonTaggedComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor args ↦ do
          let rhs : List (TSyntax `term) ←
            List.mapM
              (fun ⟨t, ty⟩ ↦ do
                let defEq ← liftCoreM $ runMetaMAsCoreM $ isDefEqGuarded ty (.const tyNameGlobal [])
                if defEq then `($defIdent $rσ $t) else `($t))
              args
          `(Parser.Term.matchAltExpr| | $ctor $((args.map Prod.fst).toArray)* => $ctor $(rhs.toArray)*)
        )

        let binderCases := List.toArray $ ← mkBinderComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor ⟨binderIdent, _⟩ otherArgs ↦ do
          let lhs := List.cons binderIdent (otherArgs.map Prod.fst)
          let binderRhs ← `($defIdent $(rσ).lift $binderIdent)
          let binderOther := otherArgs.tail.map Prod.fst
          let rhs := List.cons binderRhs $ ← binderOther.mapM identToTerm
          `(Parser.Term.matchAltExpr| | $ctor $(lhs.toArray)* => $ctor $(rhs.toArray)*)
        )

        let varCase := ← mkVarComputation (TSyntax `Lean.Parser.Term.matchAlt) (fun ctor varIdent otherArgs ↦ do
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

        _ ← mkNonTaggedComputation Unit (fun ctor args ↦ do
          let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"

          let lhsArgs := mapFst args
          let lhs ← match mapType with
          | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
          | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

          -- TODO: only push rmap/smap through to Term args
          let rhsArgs ← match mapType with
          | .is_rmap => List.mapM (fun ⟨t, _⟩ ↦ `($t⟨$rσ⟩)) args
          | .is_smap => List.mapM (fun ⟨t, _⟩ ↦ `($t[$rσ])) args
          let rhs ← `($ctor $(rhsArgs.toArray)*)

          elabCommand $ ← `(
            @[simp, grind =]
            theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
              $simpCall:tactic
          )
        )

        _ ← mkBinderComputation Unit (fun ctor ⟨binderArg, _⟩ otherArgs ↦ do
          let thmName := qualify s!"{thmPfxStr}_{ctor.getId.components.getLast!}"

          let lhsArgs := binderArg :: mapFst otherArgs
          let lhs ← match mapType with
          | .is_rmap => `(($ctor $(lhsArgs.toArray)*)⟨$rσ⟩)
          | .is_smap => `(($ctor $(lhsArgs.toArray)*)[$rσ])

          let rhsBinder ← match mapType with
          | .is_rmap => `($binderArg⟨$(rσ).lift⟩)
          | .is_smap => `($binderArg[$(rσ).lift])
          let rhsOther ← List.mapM (fun ⟨t, _⟩ ↦ `($t)) otherArgs
          let rhsArgs := rhsBinder :: rhsOther
          let rhs ← `($ctor $(rhsArgs.toArray)*)

          elabCommand $ ← `(
            @[simp, grind =]
            theorem $thmName {$(lhsArgs.toArray)*} {$rσ : $typeIdent $ty} : $lhs = $rhs := by
              $simpCall:tactic
          )
        )

        _ ← mkVarComputation Unit (fun ctor varArg otherArgs ↦ do
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

    elabCommand $ ← `(
      instance : RenMapId $ty $ty where
        apply_id := by subst_solve_id

      instance : RenMapCompose $ty $ty where
        apply_compose := by subst_solve_compose

      instance : SubstMapId $ty $ty where
        apply_id := by subst_solve_id

      instance : SubstMapStable $ty $ty where
        apply_stable := by sorry -- by subst_solve_stable

      instance : SubstMapRenComposeLeft $ty $ty where
        apply_ren_compose_left := by subst_solve_compose

      instance : SubstMapRenComposeRight $ty $ty where
        apply_ren_compose_right := by subst_solve_compose

      instance : SubstMapCompose $ty $ty where
        apply_compose := by subst_solve_compose
    )

  #leansubst_autogen Term

  #print Term.from_action
  #print Term.from_action_id
  #print Term.from_action_succ
  #print Term.from_action_su

  #print instCoe_SubstActionTerm_Term
  #check instCoe_SubstActionTerm_Term.coe

  #print Term.rmap
  #check Term.ren_app
  #check Term.ren_lam
  #check Term.ren_var

  #print Term.smap
  #check Term.subst_app
  #check Term.subst_lam
  #check Term.subst_var

  #check Term.from_action_compose
  #check Term.from_action_compose_ren

end Examples.LambdaCalcAutomation
