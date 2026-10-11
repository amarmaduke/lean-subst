module

import LeanSubst.Basic
import LeanSubst.Lemma

namespace LeanSubst

macro "lsimp " t:term : term => `(by
  solve
    | simp; exact $t
    | have lem := $t; simp at lem; simp; exact lem
    | exact ($t |> cast (by simp))
)

macro "norm_stable" : tactic => `(tactic|
  simp only [
    <-Ren.to_id,
    <-Ren.to_add,
    <-Ren.to_sub,
    <-Ren.to_cons,
    <-Ren.to_append,
    <-Ren.to_append_range,
    <-Ren.to_compose,
    <-RenVec.to_nil,
    <-RenVec.to_cons,
    <-RenVec.to_head,
    <-RenVec.to_tail,
    <-RenVec.to_lift,
    Subst.to_compose_left,
    Subst.to_compose_right,
    Subst.smap_to
  ])

macro "subst_solve_id" : tactic => `(tactic| {
  intro s; induction s
  all_goals
    simp [*]
})

macro "subst_solve_stable" : tactic => `(tactic| {
  intro r σ h; subst h
  funext; case _ t =>
  induction t generalizing r
  all_goals
    solve
      | simp [*]; try norm_stable
      | repeat (cases r; case' _ r => try simp only)
        simp [*]; try norm_stable
      | repeat (cases r; case' _ r => try simp only)
        simp [*]; congr
})

macro "subst_solve_compose" : tactic => `(tactic| {
  intro s a b
  induction s generalizing a b
  all_goals simp [*]; try rfl
  all_goals
    repeat (cases a; case' _ a => try simp only)
    repeat (cases b; case' _ b => try simp only)
    simp [*]
})

end LeanSubst
