
namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2} {U : Type u3}

structure Ren (T : Type u2) where
  act : Nat -> Nat

class RenMap (S : Type u1) (T : Type u2) where
  rmap : Ren T -> S -> S

export RenMap (rmap)

macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)

@[app_unexpander rmap]
def unexpand_rmap : Lean.PrettyPrinter.Unexpander
| `($_ $r $t) => `($t⟨$r⟩)
| _ => throw ()

inductive Action (T : Type u2) where
| re : Nat -> Action T
| su : T -> Action T
deriving Repr

export Action (re su)

structure Subst (T : Type u2) where
  inner : Nat -> Action T

class SubstAction (T : Type u1) (A : Type u2) (U : outParam (Type u3)) where
  act (σ : Subst T) : A -> U

def Subst.act [SubstAction S T U] (σ : Subst S) : T -> U := SubstAction.act σ

instance : SubstAction T Nat (Action T) where
  act := Subst.inner

class SubstMap (S : Type u1) (T : Type u2) where
  smap : Subst T -> S -> S

export SubstMap (smap)

macro:max t:term noWs "[" σ:term "]" : term => `(smap $σ $t)

@[app_unexpander smap]
def unexpand_smap : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t) => `($t[$σ])
| _ => throw ()

end LeanSubst
