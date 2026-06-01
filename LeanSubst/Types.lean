
namespace LeanSubst
  universe u1 u2
  variable {S : Type u1} {T : Type u2}

  structure Ren where
    act : Nat -> Nat

  structure HetRen (T : Type u1) where
    act : Nat -> Nat

  inductive Subst.Action (T : Type u1) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  structure Subst (T : Type u1) where
    act : Nat -> Subst.Action T



end LeanSubst
