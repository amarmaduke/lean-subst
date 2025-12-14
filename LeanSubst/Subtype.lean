-- import LeanSubst.Basic

-- namespace LeanSubst
--   universe u

--   class SubtypeInject {T : Type u} (P : T -> Prop) where
--     inj : T -> {t:T // P t}
--     inj_stable {t} : (p : P t) -> (inj t) = ⟨t, p⟩

--   namespace Subtype
--     variable {T : Type} (P : T -> Prop)

--     @[simp]
--     def prj : (Nat -> Subst.Action {t:T // P t}) -> Nat -> Subst.Action T
--     | σ, n =>
--       match σ n with
--       | .re k => .re k
--       | .su t => .su t

--     theorem prj_ren (r : Ren) : prj P r.to = r.to := by
--       funext; case _ x =>
--       cases x <;> simp [Ren.to]

--     @[simp]
--     theorem prj_I : prj P +0 = +0 := by
--       have lem := prj_ren P (λ x => x); simp at lem
--       apply lem

--     @[simp]
--     theorem prj_S : prj P +1 = +1 := by
--       have lem := prj_ren P (· + 1); simp at lem
--       apply lem

--     variable [i1 : SubtypeInject P] [i2 : SubstMap T]

--     @[simp]
--     def inj : (Nat -> Subst.Action T) -> (Nat -> Subst.Action {t:T // P t})
--     | σ, n =>
--       match σ n with
--       | .re k => .re k
--       | .su t => .su (SubtypeInject.inj t)

--     omit [SubstMap T] in
--     theorem prj_inj (σ : Subst {x:T // P x}) : (inj P ∘ prj P) σ = σ := by
--       funext; case _ x =>
--       simp; generalize zdef : σ x = z
--       cases z <;> simp
--       case _ t =>
--       cases t; case _ t p =>
--       simp; apply SubtypeInject.inj_stable

--     @[simp]
--     def lift : (k : Subst.Kind) -> Subst.Lift {t:T // P t} k -> Subst.Lift T k
--     | .re, lf, f => lf f
--     | .su, lf, f => prj P $ lf (inj P f)

--     -- @[simp]
--     -- def rlift : Subst.Lift T -> Subst.Lift {t:T // P t}
--     -- | lf, f => inj P $ lf (prj P f)

--     omit [SubstMap T] in
--     @[simp]
--     theorem lift_ren_lift : lift P .re Ren.lift = Ren.lift := by
--       funext; case _ σ x => simp

--     class SubstMapClosed {T : Type} [SubstMap T] (P : T -> Prop) [SubtypeInject P] where
--       closed : ∀ lf f t, P t -> P (SubstMap.smap .su (lift P .su lf) (prj P f) t)

--     @[simp]
--     def smap [i : SubstMapClosed P] :
--       (k : Subst.Kind) ->
--       Subst.Lift {t:T // P t} k ->
--       SplitSubst {t:T // P t} k ->
--       {t:T // P t} -> {t:T // P t}
--     | .re, lf, f, .mk t p => .mk (SubstMap.smap .re Ren.lift f t) sorry
--     | .su, lf, f, .mk t p => .mk (SubstMap.smap .su (lift P .su lf) (prj P f) t) (i.closed lf f t p)

--     variable [i3 : SubstMapClosed P]

--     instance instSubstMap : SubstMap {t:T // P t} where
--       smap := smap P

--     theorem prop_ren : ∀ (r : Ren) t, P t -> P (Ren.apply r t) := by
--       intro r t h; unfold Ren.apply
--       have lem := i3.closed (Ren.to ∘ Ren.lift ∘ Ren.fro) r.to t h
--       rw [lift_ren_lift, prj_ren] at lem
--       apply lem

--     @[simp]
--     theorem ren_apply_mk {t p} (r : Ren)
--       : Ren.apply r (Subtype.mk t p) = Subtype.mk (Ren.apply r t) (prop_ren P r t p)
--     := by
--       unfold Ren.apply; unfold SubstMap.smap
--       unfold instSubstMap; simp
--       rw [prj_ren, lift_ren_lift]
--       unfold SubstMap.smap; simp

--     class SubstMapLift [i : SubstMap T] [SubstMapClosed P] where
--       lift_eq : ∀ σ t,
--         i.smap (lift P Subst.lift) (prj P σ) t = i.smap Subst.lift (prj P σ) t

--     variable [i4 : SubstMapLift P]

--     theorem prop_subst : ∀ (σ : Subst {x:T // P x}) t, P t -> P t[prj P σ] := by
--       intro σ t h
--       unfold Subst.apply
--       rw [<-i4.lift_eq]
--       apply i3.closed
--       apply h

--     @[simp]
--     theorem subst_mk {t p} {σ : Subst {x:T // P x}}
--       : (Subtype.mk t p)[σ] = Subtype.mk t[prj P σ] (prop_subst P σ t p)
--     := by
--       conv => {
--         lhs; unfold Subst.apply; unfold SubstMap.smap
--         unfold instSubstMap; simp
--       }
--       apply Subtype.eq; simp
--       unfold Subst.apply; unfold SubstMap.smap
--       apply i4.lift_eq

--     @[simp]
--     theorem prj_compose {σ τ : Subst {x:T // P x}} : prj P (σ ∘ τ) = prj P σ ∘ prj P τ := by
--       funext; case _ x =>
--       simp [Subst.compose]
--       generalize zdef : σ x = z at *
--       cases z <;> simp
--       case _ t =>
--         cases t; case _ t p =>
--         simp

--     variable [i5 : SubstMapStable T]

--     theorem apply_id {t : {x:T // P x}} : t[I] = t := by
--       cases t; case _ t p =>
--       simp

--     theorem apply_stable {r : Ren} {σ : Subst {x:T // P x}}
--       : r.to = σ -> Ren.apply r = Subst.apply σ
--     := by
--       intro h
--       funext; case _ x =>
--       cases x; case _ x p =>
--       simp
--       have lem1 : r.to = prj P σ := by
--         funext; case _ z =>
--         have lem1 : r.to z = σ z := by rw [h]
--         simp [Ren.to]
--         generalize wdef : σ z = w at *
--         cases w <;> simp [Ren.to] at *
--         case _ q => rw [lem1]
--       have lem1 := i5.apply_stable lem1
--       rw [lem1]

--     instance SubstMapStable_Term : SubstMapStable {x:T // P x} where
--       apply_id := apply_id P
--       apply_stable := apply_stable P

--     variable [i6 : SubstMapCompose T]

--     omit [SubstMapStable T] in
--     theorem apply_compose {s} {σ τ : Subst {x:T // P x}} : s[σ][τ] = s[σ ∘ τ] := by
--       cases s; case _ s p =>
--       simp

--     instance SubstMapCompose_Term : SubstMapCompose {x:T // P x} where
--       apply_compose := apply_compose P

--   end Subtype

-- end LeanSubst
