-- import LeanSubst

-- namespace LeanSubst.Examples.ArityGeneric

--   inductive Kind where
--   | ctor | bind

--   inductive Term (V : Type) (α : V -> Nat) (β : V -> Kind -> Prop) where
--   | var : Nat -> Term V α β
--   | bind : (v:{v:V // β v .bind}) -> ({k:Nat // k < α v} -> Term V α β) -> Term V α β -> Term V α β
--   | ctor : (v:{v:V // β v .ctor}) -> ({k:Nat // k < α v} -> Term V α β) -> Term V α β
--   | variadic n : Term V α β -> ({k:Nat // k < n} -> Term V α β) -> Term V α β

--   variable {V : Type} {α : V -> Nat} {β : V -> Kind -> Prop}

--   @[coe]
--   def Term.from_action : Subst.Action (Term V α β) -> Term V α β
--   | .re y => var y
--   | .su t => t

--   @[simp]
--   theorem Term.from_action_id {n}
--     : from_action (+0 n) = @var V α β n
--   := by
--     simp [from_action, Subst.id]

--   @[simp]
--   theorem Term.from_action_succ {n}
--     : from_action (+1 n) = @var V α β (n + 1)
--   := by
--     simp [from_action, Subst.succ]

--   @[simp]
--   theorem Term.from_acton_re {n}
--     : from_action (.re n) = @var V α β n
--   := by simp [from_action]

--   @[simp]
--   theorem Term.from_action_su {t : Term V α β} : from_action (.su t) = t := by simp [from_action]

--   instance instCoe_SubstActionTerm_Term : Coe (Subst.Action (Term V α β)) (Term V α β) where
--     coe := Term.from_action

--   @[simp]
--   def smap (k : Subst.Kind) (lf : Subst.Lift (Term V α β) k) (f : SplitSubst (Term V α β) k)
--     : Term V α β -> Term V α β
--   | .var x =>
--     match k with
--     | .re => .var (f x)
--     | .su => f x
--   | .bind v ts t => .bind v (λ i => smap k lf f (ts i)) (smap k lf (lf f) t)
--   | .ctor v ts => .ctor v (λ i => smap k lf f (ts i))
--   | .variadic n t ts => .variadic n (smap k lf f t) (λ i => smap k lf f (ts i))

--   instance SubstMap_Term : SubstMap (Term V α β) where
--     smap := smap

--   @[simp]
--   theorem subst_var {x} {σ : Subst (Term V α β)} : (.var x)[σ] = σ x := by
--     unfold Subst.apply; simp [SubstMap.smap]

--   @[simp]
--   theorem subst_bind {v ts t} {σ : Subst (Term V α β)}
--     : (.bind v ts t)[σ] = .bind v (λ k => (ts k)[σ]) t[σ.lift]
--   := by
--     unfold Subst.apply; simp [SubstMap.smap]

--   @[simp]
--   theorem subst_ctor {v ts} {σ : Subst (Term V α β)}
--     : (.ctor v ts)[σ] = .ctor v (λ k => (ts k)[σ])
--   := by
--     unfold Subst.apply; simp [SubstMap.smap]

--   @[simp]
--   theorem subst_variadic {n t ts} {σ : Subst (Term V α β)}
--     : (.variadic n t ts)[σ] = .variadic n t[σ] (λ k => (ts k)[σ])
--   := by
--     unfold Subst.apply; simp [SubstMap.smap]

--   @[simp]
--   theorem Term.from_action_compose {x} {σ τ : Subst (Term V α β)}
--     : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
--   := by
--     simp [Term.from_action, Subst.compose]
--     generalize zdef : σ x = z
--     cases z <;> simp [Term.from_action]

--   theorem apply_id {t : Term V α β} : t[+0] = t := by
--     induction t
--     all_goals (simp at * <;> try simp [*])

--   theorem apply_stable (r : Ren) (σ : Subst (Term V α β))
--     : r = σ -> Ren.apply r = Subst.apply σ
--   := by solve_stable r, σ

--   instance SubstMapStable_Term : SubstMapStable (Term V α β) where
--     apply_id := apply_id
--     apply_stable := apply_stable

--   theorem apply_compose {s} {σ τ : Subst (Term V α β)} : s[σ][τ] = s[σ ∘ τ] := by
--     solve_compose Term V α β, s, σ, τ

-- end LeanSubst.Examples.ArityGeneric
