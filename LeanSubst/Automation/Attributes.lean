import Batteries.Lean.TagAttribute
import Lean.Parser.Term
import Lean.Elab

open Lean Elab Tactic Meta Command

initialize leanSubstVar : TagAttribute ← registerTagAttribute `leansubst_var "Indicates that a constructor is a variable constructor."

#check Lean.Parser.Command.classAbbrev
#check Lean.Parser.Term.attrInstance
#check Attr.coe

#check Lean.Parser.Attr.simple

#check mkElabAttribute

syntax (name := leansubst_binder_attr) "leansubst_binder" "(" term "," num "," term ")" : attr

initialize leanSubstBinder : ParametricAttribute (Term × Nat × Term) ← registerParametricAttribute {
  name := `leansubst_binder_attr,
  descr := "Blah",
  getParam := fun
    | name, stx@`(attr| leansubst_binder ($ty, $pos, $nBnd)) => do
      dbg_trace s!"ty: {ty}"
      dbg_trace s!"inArg: {pos}"
      dbg_trace s!"nBnd: {nBnd}"

      pure (ty, pos.getNat, nBnd)
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

elab "#leansubst" "bind" nBndClosure:term "of" ty:term "in" ctor:ident "at_pos" pos:num : command => do
  let nBndClosure ← match nBndClosure with
  | `($n:num) => `(fun _ => $n)
  | closure => pure closure
  elabCommand $ ← `(
    attribute [leansubst_binder ($ty, $pos, $nBndClosure)] $ctor
  )

elab "#leansubst" "var" ctor:ident : command => do
  elabCommand $ ← `(
    attribute [leansubst_var] $ctor
  )

elab "#leansubst" "invoke" : command => sorry
