import Batteries.Lean.TagAttribute
import Lean.Elab

namespace LeanSubstAttributes

  open Lean Elab Tactic Meta Command

  initialize leanSubstVar : TagAttribute ← registerTagAttribute `leansubst_var "Indicates that a constructor is a variable constructor."

  #check Lean.Parser.Command.classAbbrev
  #check Lean.Parser.Term.attrInstance
  #check Attr.coe

  #check Lean.Parser.Attr.simple

  #check mkElabAttribute

  declare_syntax_cat leansubst_attr

  syntax "(" term "," term "," num ")" : leansubst_attr

  syntax (name := leansubst_binder_attr) "leansubst_binder" "[" term,* "]" "[" term,* "]" "[" num,* "]" : attr

  initialize leanSubstBinder : ParametricAttribute $ List (Term × Term × Nat) ← registerParametricAttribute {
    name := `leansubst_binder_attr,
    descr := "Blah",
    getParam := fun
    | name, stx@`(attr| leansubst_binder [ $closures,* ] [ $tys,* ] [ $ps,* ]) => do
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
      dbg_trace s!"aw fuck {name}, {stx}"
      pure 0
  }

  declare_syntax_cat bind_data

  syntax term " of " term " at " " pos " num : bind_data

  syntax term " at " " pos " num : bind_data

  macro ty:term " at " " pos " p:num : bind_data => `(bind_data| 1 of $ty at pos $p)

  declare_syntax_cat bind_decl

  syntax " bind " bind_data,+ " in " ident : bind_decl

  elab "#leansubst" stx:bind_decl : command => stx |> fun
  | `(bind_decl| bind $data,* in $ctor) => do
    let mapfun := fun
    | `(bind_data| $closure:term of $ty:term at pos $p) => pure (closure, ty, p)
    | `(bind_data| $ty:term at pos $p) => pure (Syntax.mkNatLit 1, ty, p) -- I thought the macros would be expanded, but this seems necessary
    | _ => throwUnsupportedSyntax
    let data ← data.getElems.mapM mapfun
    let closures := data.map (·.1)
    let tys := data.map (·.2.1)
    let ps : Array (TSyntax `num) := data.map (·.2.2)
    dbg_trace "Elabbing command"
    elabCommand $ ← `(
      attribute [leansubst_binder [$closures,*] [$tys,*] [$ps,*]] $ctor
    )
    dbg_trace "Done!"
  | _ => throwUnsupportedSyntax


  elab "#leansubst" "var" ctor:ident : command => do
    elabCommand $ ← `(
      attribute [leansubst_var] $ctor
    )

  elab "#leansubst" "generate" : command => sorry

end LeanSubstAttributes
