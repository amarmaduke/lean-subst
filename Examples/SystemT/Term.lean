
import LeanSubst
open LeanSubst

namespace SystemT

inductive Ty where
| nat | top | bot : Ty
| arrow : Ty -> Ty -> Ty
| prod : Ty -> Ty -> Ty
| sum : Ty -> Ty -> Ty

notation "ℕ" => Ty.nat
notation "⊤" => Ty.top
notation "⊥" => Ty.bot
infixr:64 " -:> " => Ty.arrow
infixl:63 " `× " => Ty.prod
infixl:62 " `+ " => Ty.sum

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term
| unit : Term
| pair : Term -> Term -> Term
| proj : Nat -> Term -> Term
| absurd : Ty -> Term -> Term
| split : Term -> Term -> Term -> Term
| inj : Ty -> Nat -> Term -> Term
| zero : Term
| succ : Term -> Term
| nrec : Term -> Term -> Term -> Term

prefix:max "#" => Term.var
notation "λ[" A "]" t => Term.lam A t
notation f " `• " a => Term.app f a
notation "`()" => Term.unit
notation "`⟨" t "," s "⟩" => Term.pair t s
postfix:max ".!1" => Term.proj 1
postfix:max ".!2" => Term.proj 2
notation "`0" => Term.zero
postfix:max " `+1" => Term.succ

#leansubst var Term.var
#leansubst bind Term at pos 1 in Term.lam
#leansubst bind Term at pos 1, Term at pos 2 in Term.split
#leansubst bind 2 of Term at pos 2 in Term.nrec
#leansubst generate Term

end SystemT
