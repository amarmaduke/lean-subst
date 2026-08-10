
namespace LeanSubst.Metatheory

mutual
  inductive Term where
  | const : Nat -> Term
  | inst : Term -> Subst -> Term

  inductive Subst where
  | var : Nat -> Subst
  | shift : Subst
  | re : Nat -> Subst -> Subst
  | su : Term -> Subst -> Subst
  | compose : Subst -> Subst -> Subst
end

end LeanSubst.Metatheory
