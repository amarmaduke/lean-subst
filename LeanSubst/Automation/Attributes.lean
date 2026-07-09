import Batteries.Lean.TagAttribute
import Lean.Parser.Term

open Lean

initialize leanSubstVar : TagAttribute ← registerTagAttribute `leansubst_var "Indicates that a constructor is a variable constructor."
initialize leanSubstBinder : TagAttribute ← registerTagAttribute `leansubst_binder "Indicates that a constructor is a binder constructor."

#check Lean.Parser.Command.classAbbrev
#check Lean.Parser.Term.attrInstance
#check Attr.coe

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
