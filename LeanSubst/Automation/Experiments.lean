import LeanSubst
import LeanSubst.Automation.Basic

namespace LambdaCalcTest

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term
  deriving BEq

  prefix:100 ":λ " => Term.lam
  infixl:65 " :@ " => Term.app

  attribute [leansubst_binder' 0] Term.lam
  -- attribute [leansubst_binder (Term, 0, fun _ => 0)] Term.lam
  #leansubst var Term.var
  #leansubst bind 1 of Term in Term.lam at_pos 0

  #leansubst_autogen Term

  #print Term.from_action
  #print Term.from_action_id
  #print Term.from_action_succ
  #print Term.from_action_su

  #print instCoe_SubstActionTerm_Term
  #check instCoe_SubstActionTerm_Term.coe

  #print Term.rmap
  #check Term.ren_app
  #check Term.ren_lam
  #check Term.ren_var

  #print Term.smap
  #check Term.subst_app
  #check Term.subst_lam
  #check Term.subst_var

  #check Term.from_action_compose
  #check Term.from_action_compose_ren

end LambdaCalcTest

namespace SystemFTest

  inductive Ty where
  | var : Nat -> Ty
  | arr : Ty -> Ty -> Ty
  | all : Ty -> Ty

  attribute [leansubst_var] Ty.var
  attribute [leansubst_binder' 0] Ty.all

  prefix:max "t#" => Ty.var
  infixr:85 "-:>" => Ty.arr
  notation ":∀" t => Ty.all t

  inductive Term where
  | var : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Ty -> Term -> Term
  | tapp : Term -> Ty -> Term
  | tlam : Term -> Term

  attribute [leansubst_var] Term.var
  attribute [leansubst_binder' 0] Term.tlam
  attribute [leansubst_binder' 1] Term.lam

  prefix:max "#" => Term.var
  infixl:65 "•" => Term.app
  notation:100 "λ[" A "]" t => Term.lam A t
  notation:65 f "•[" a "]" => Term.tapp f a
  notation:100 "Λ" t => Term.tlam t

  -- Ty --
  #leansubst_autogen Ty

  #print Ty.from_action
  #print Ty.from_action_id
  #print Ty.from_action_succ
  #print Ty.from_action_su

  #print instCoe_SubstActionTy_Ty
  #check instCoe_SubstActionTy_Ty.coe

  #print Ty.rmap
  #check Ty.ren_arr
  #check Ty.ren_all
  #check Ty.ren_var

  #print Ty.smap
  #check Ty.subst_arr
  #check Ty.subst_all
  #check Ty.subst_var

  #check Ty.from_action_compose
  #check Ty.from_action_compose_ren

  -- Term --
  #leansubst_autogen Term

  #print Term.from_action
  #print Term.from_action_id
  #print Term.from_action_succ
  #print Term.from_action_su

  #print instCoe_SubstActionTerm_Term
  #check instCoe_SubstActionTerm_Term.coe

  #print Term.rmap
  #check Term.ren_app
  #check Term.ren_lam
  #check Term.ren_var

  #print Term.smap
  #check Term.subst_app
  #check Term.subst_lam
  #check Term.subst_var

  #check Term.from_action_compose
  #check Term.from_action_compose_ren

end SystemFTest
