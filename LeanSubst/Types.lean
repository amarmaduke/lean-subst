
namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2}

structure Ren where
  act : Nat -> Nat

class RenMap (S : Type u1) where
  rmap : Ren -> S -> S

export RenMap (rmap)

macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)

structure HetRen (T : Type u2) where
  act : Nat -> Nat

class HetRenMap (S : Type u1) (T : Type u2) where
  hrmap : HetRen T -> S -> S

export HetRenMap (hrmap)

inductive Subst.Action (S : Type u1) where
| re : Nat -> Subst.Action S
| su : S -> Subst.Action S
deriving Repr

export Subst.Action (re su)

structure Subst (S : Type u1) where
  act : Nat -> Subst.Action S

class SubstMap (S : Type u1) where
  smap : Subst S -> S -> S

export SubstMap (smap)

structure HetSubst (S : Type u1) (T : Type u2) where
  act : Nat -> Subst.Action S

class HetSubstMap (S : Type u1) (T : Type u2) where
  hsmap : HetSubst S T -> S -> S

export HetSubstMap (hsmap)

end LeanSubst
