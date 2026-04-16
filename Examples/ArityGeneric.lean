import LeanSubst
import Lilac
open Lilac

namespace LeanSubst.Examples.ArityGeneric

  inductive VariantSort where
  | ctor | bind

  inductive Term (V : VariantSort -> Nat -> Prop) where
  | var : Nat -> Term V
  | bind {n} : V .bind n -> Fun.Vec (Term V) n -> Term V -> Term V
  | ctor {n} : V .ctor n -> Fun.Vec (Term V) n -> Term V
  | variadic n : Term V -> Fun.Vec (Term V) n -> Term V

  variable {V : VariantSort -> Nat -> Prop}

  @[coe]
  def Term.from_action : Subst.Action (Term V) -> Term V
  | .re y => var y
  | .su t => t

  @[simp]
  theorem Term.from_action_id {n}
    : from_action (+0 n) = @var V n
  := by
    simp [from_action, Subst.id]

  @[simp]
  theorem Term.from_action_succ {n}
    : from_action (+1 n) = @var V (n + 1)
  := by
    simp [from_action, Subst.succ]

  @[simp]
  theorem Term.from_acton_re {n}
    : from_action (.re n) = @var V n
  := by simp [from_action]

  @[simp]
  theorem Term.from_action_su {t : Term V} : from_action (.su t) = t := by simp [from_action]

  instance instCoe_SubstActionTerm_Term : Coe (Subst.Action (Term V)) (Term V) where
    coe := Term.from_action

  @[simp]
  def Term.rmap (r : Ren) : Term V -> Term V
  | var x => var (r x)
  | bind v ts t => bind v (rmap r <$> ts) (rmap r.lift t)
  | ctor v ts => ctor v (rmap r <$> ts)
  | variadic n t ts => variadic n (rmap r t) (rmap r <$> ts)

  instance : RenMap (Term V) where
    rmap := Term.rmap

  @[simp]
  theorem Term.ren_var {x} {r : Ren} : (Term.var (V := V) x)⟨r⟩ = .var (r x) := by
    simp [RenMap.rmap]

  @[simp]
  theorem Term.ren_bind {n} {v : V .bind n} {ts t} {r : Ren}
    : (bind v ts t)⟨r⟩ = .bind v (λ k => (ts k)⟨r⟩) t⟨r.lift⟩
  := by
    simp [RenMap.rmap]

  @[simp]
  theorem Term.ren_ctor {n} {v : V .ctor n} {ts} {r : Ren}
    : (Term.ctor v ts)⟨r⟩ = .ctor v (λ k => (ts k)⟨r⟩)
  := by
    simp [RenMap.rmap]

  @[simp]
  theorem Term.ren_variadic {n} {t : Term V} {ts} {r : Ren}
    : (Term.variadic n t ts)⟨r⟩ = .variadic n t⟨r⟩ (λ k => (ts k)⟨r⟩)
  := by
    simp [RenMap.rmap]

  instance : RenMapId (Term V) where
    apply_id := by intro t; induction t <;> simp [*]

  instance : RenMapCompose (Term V) where
    apply_compose := by intro t r1 r2; induction t generalizing r1 r2 <;> simp [*]

  @[simp]
  def Term.smap (σ : Subst (Term V)) : Term V -> Term V
  | var x => σ x
  | bind v ts t => bind v (smap σ <$> ts) (smap σ.lift t)
  | ctor v ts => ctor v (smap σ <$> ts)
  | variadic n t ts => variadic n (smap σ t) (smap σ <$> ts)

  instance : SubstMap (Term V) (Term V) where
    smap := Term.smap

  @[simp]
  theorem Term.subst_var {x} {σ : Subst (Term V)} : (.var x)[σ] = σ x := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.subst_bind {n} {v : V .bind n} {ts t} {σ : Subst (Term V)}
    : (bind v ts t)[σ:Term V] = .bind v (λ k => (ts k)[σ]) t[σ.lift]
  := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.subst_ctor {n} {v : V .ctor n} {ts} {σ : Subst (Term V)}
    : (.ctor v ts)[σ] = .ctor v (λ k => (ts k)[σ])
  := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.subst_variadic {n t ts} {σ : Subst (Term V)}
    : (.variadic n t ts)[σ] = .variadic n t[σ] (λ k => (ts k)[σ])
  := by
    simp [SubstMap.smap]

  @[simp]
  theorem Term.from_action_compose {x} {σ τ : Subst (Term V)}
    : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
  := by
    simp [Term.from_action, Subst.compose]
    generalize zdef : σ x = z
    cases z <;> simp [Term.from_action]

  instance : SubstMapId (Term V) (Term V) where
    apply_id := by subst_solve_id

  instance : SubstMapStable (Term V) where
    apply_stable := by subst_solve_stable

  instance : SubstMapRenComposeLeft (Term V) (Term V) where
    apply_ren_compose_left := by subst_solve_compose

  instance : SubstMapRenComposeRight (Term V) (Term V) where
    apply_ren_compose_right := by subst_solve_compose

  instance : SubstMapCompose (Term V) (Term V) where
    apply_compose := by subst_solve_compose

end LeanSubst.Examples.ArityGeneric
