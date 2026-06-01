
namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2}

structure Ren where
  act : Nat -> Nat

class RenMap (S : Type u1) where
  rmap : Ren -> S -> S

export RenMap (rmap)

macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ $r $t) => `($t⟨$r⟩)
| _ => throw ()

structure HetRen (T : Type u2) where
  act : Nat -> Nat

class HetRenMap (S : Type u1) (T : Type u2) where
  hrmap : HetRen T -> S -> S

export HetRenMap (hrmap)

macro:max t:term noWs "⟨" r:term "⟩" : term => `(hrmap $r $t)

@[app_unexpander rmap]
def unexpand_hrmap : Lean.PrettyPrinter.Unexpander
| `($_ $r $t) => `($t⟨$r⟩)
| _ => throw ()

inductive Action (S : Type u1) where
| re : Nat -> Action S
| su : S -> Action S
deriving Repr

export Action (re su)

structure Subst (S : Type u1) where
  act : Nat -> Action S

class SubstMap (S : Type u1) where
  smap : Subst S -> S -> S

export SubstMap (smap)

macro:max t:term noWs "[" σ:term "]" : term => `(smap $σ $t)

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t) => `($t[$σ])
| _ => throw ()

structure HetSubst (S : Type u1) (T : Type u2) where
  act : Nat -> Action T

class HetSubstMap (S : Type u1) (T : Type u2) where
  hsmap : HetSubst S T -> S -> S

export HetSubstMap (hsmap)

macro:max t:term noWs "[" σ:term "]" : term => `(hsmap $σ $t)

@[app_unexpander smap]
def unexpand_hsmap : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t) => `($t[$σ])
| _ => throw ()

end LeanSubst
