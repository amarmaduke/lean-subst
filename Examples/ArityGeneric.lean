import LeanSubst

namespace LeanSubst.Examples.ArityGeneric

  inductive Kind where
  | ctor | bind

  inductive Term (V : Type) (α : V -> Nat) (β : V -> Kind -> Prop) where
  | var : Nat -> Term V α β
  | bind : (v:{v:V // β v .bind}) -> ({k:Nat // k < α v} -> Term V α β) -> Term V α β -> Term V α β
  | ctor : (v:{v:V // β v .ctor}) -> ({k:Nat // k < α v} -> Term V α β) -> Term V α β
  | variadic n : Term V α β -> ({k:Nat // k < n} -> Term V α β) -> Term V α β

  variable {V : Type} {α : V -> Nat} {β : V -> Kind -> Prop}

  namespace Term
    @[simp, coe]
    def var_coe : Subst.Action (Term V α β) -> Term V α β
    | .re y => .var y
    | .su t => t

    instance : Coe (Subst.Action (Term V α β)) (Term V α β) where
      coe := var_coe
  end Term

  @[simp]
  def smap (lf : Subst.Lift (Term V α β)) (f : Nat -> Subst.Action (Term V α β)) : Term V α β -> Term V α β
  | .var x => f x
  | .bind v ts t => .bind v (λ k => smap lf f (ts k)) (smap lf (lf f) t)
  | .ctor v ts => .ctor v (λ k => smap lf f (ts k))
  | .variadic n t ts => .variadic n (smap lf f t) (λ k => smap lf f (ts k))

  instance SubstMap_Term : SubstMap (Term V α β) where
    smap := smap

  @[simp]
  theorem subst_var {x} {σ : Subst (Term V α β)} : (.var x)[σ] = σ x := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_bind {v ts t} {σ : Subst (Term V α β)}
    : (.bind v ts t)[σ] = .bind v (λ k => (ts k)[σ]) t[σ.lift]
  := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_ctor {v ts} {σ : Subst (Term V α β)}
    : (.ctor v ts)[σ] = .ctor v (λ k => (ts k)[σ])
  := by
    unfold Subst.apply; simp [SubstMap.smap]

  @[simp]
  theorem subst_variadic {n t ts} {σ : Subst (Term V α β)}
    : (.variadic n t ts)[σ] = .variadic n t[σ] (λ k => (ts k)[σ])
  := by
    unfold Subst.apply; simp [SubstMap.smap]

  theorem apply_id {t : Term V α β} : t[I] = t := by
    induction t
    all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst (Term V α β)}
    : r.to = σ -> Ren.apply r = Subst.apply σ
  := by solve_stable r, σ

  instance SubstMapStable_Term : SubstMapStable (Term V α β) where
    apply_id := apply_id
    apply_stable := apply_stable

  theorem apply_compose {s} {σ τ : Subst (Term V α β)} : s[σ][τ] = s[σ ∘ τ] := by
    solve_compose (Term V α β), s, σ, τ

end LeanSubst.Examples.ArityGeneric
