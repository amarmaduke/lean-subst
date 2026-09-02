import Lean.Elab

namespace LeanSubstAttributes

  open Lean Elab Tactic Meta Command

  initialize leanSubstVar : TagAttribute ← registerTagAttribute `_leansubst_var "Indicates that a constructor is a variable constructor."

  #check Lean.Parser.Command.classAbbrev
  #check Lean.Parser.Term.attrInstance
  #check Attr.coe

  #check Lean.Parser.Attr.simple

  #check mkElabAttribute

  syntax (name := leansubst_binder_attr) "_leansubst_binder" "[" term,* "]" "[" ident,* "]" "[" num,* "]" : attr

  initialize leanSubstBinder : ParametricAttribute $ List (Term × Ident × Nat) ← registerParametricAttribute {
    name := `leansubst_binder_attr,
    descr := "Blah",
    getParam := fun
    | name, stx@`(attr| _leansubst_binder [ $closures,* ] [ $tys,* ] [ $ps,* ]) => do
      let ret := Array.zip closures.getElems (Array.zip tys.getElems ps.getElems)
      pure $ ret.toList.map (fun (a, b, c) => (a, b, c.getNat))
    | _, _ => throwUnsupportedSyntax
  }

  initialize leanSubstBinder' : ParametricAttribute Nat ← registerParametricAttribute {
    name := `leansubst_binder',
    descr := "Blah",
    getParam := fun
    | name, stx@`(Lean.Parser.Attr.simple| $_ $n:num) => do
      pure n.getNat
    | name, stx@`(Lean.Parser.Term.attrInstance| $_) => do
      dbg_trace s!"oh no {name}, {stx}"
      pure 0
  }

  declare_syntax_cat bind_data (behavior := symbol)

  syntax term &" of " term &" at " &" pos " num : bind_data

  syntax term &" at " &" pos " num : bind_data

  declare_syntax_cat bind_decl (behavior := symbol)

  syntax " bind " bind_data,+ &" in " ident : bind_decl

  elab "#leansubst" stx:bind_decl : command => stx |> fun
  | `(bind_decl| bind $data:bind_data,* in $ctor) => do
    let mapfun := fun
    | `(bind_data| $closure:term of $ty:ident at pos $p) => pure (closure, ty, p)
    | `(bind_data| $ty:ident at pos $p) => pure (Syntax.mkNatLit 1, ty, p)
    | _ => throwUnsupportedSyntax
    let data ← data.getElems.mapM mapfun
    let closures := data.map (·.1)
    let tys := data.map (·.2.1)
    let ps : Array (TSyntax `num) := data.map (·.2.2)
    elabCommand $ ← `(
      attribute [_leansubst_binder [$closures,*] [$tys,*] [$ps,*]] $ctor
    )
  | _ => throwUnsupportedSyntax

  declare_syntax_cat var_decl (behavior := symbol)

  syntax " var " ident : var_decl

  syntax " var " ident &" at " &" pos " num : var_decl

  -- elab "#leansubst" stx:var_decl : command => stx |> fun
  -- | `(var_decl| var $ctor at pos $n) => do
  --   elabCommand $ ← `(
  --     attribute [_leansubst_var $n] $ctor
  --   )
  -- |  `(var_decl| var $ctor) => do
  --   elabCommand $ ← `(
  --     attribute [_leansubst_var 0] $ctor
  --   )
  -- | _ => throwUnsupportedSyntax

  elab "#leansubst" &" var " ctor:ident : command => do
    elabCommand $ ← `(
      attribute [_leansubst_var] $ctor
    )

end LeanSubstAttributes
