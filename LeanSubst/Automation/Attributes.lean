import Batteries.Lean.TagAttribute

open Lean

initialize leanSubstVar : TagAttribute ← registerTagAttribute `leansubst_var "Indicates that a constructor is a variable constructor."
initialize leanSubstBinder : TagAttribute ← registerTagAttribute `leansubst_binder "Indicates that a constructor is a binder constructor."
