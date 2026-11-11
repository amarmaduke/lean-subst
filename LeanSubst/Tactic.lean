module

public meta import Lean.Meta.Tactic.Simp

open Lean.Parser.Tactic

register_simp_attr subst_rw
register_simp_attr subst_to
register_simp_attr subst_data

syntax (name := norm_subst) "norm_subst"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

macro_rules
| `(tactic| norm_subst) =>
  `(tactic| simp only [subst_rw, subst_to, subst_data])
| `(tactic| norm_subst at $h) =>
  `(tactic| simp only [subst_rw, subst_to, subst_data] at $h)
| `(tactic| norm_subst [ $h,* ]) =>
  `(tactic| simp only [subst_rw, subst_to, subst_data, $h,*])
| `(tactic| norm_subst [ $h1,* ] at $h2) =>
  `(tactic| simp only [subst_rw, subst_to, subst_data, $h1,*] at $h2)

syntax (name := simp_mod) "simp%"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? term : term

macro_rules
| `(simp% $t) => `(by
  solve
    | simp; exact $t
    | have lem := $t; simp at lem; simp; exact lem
    | exact ($t |> cast (by simp)))
| `(simp% [ $h,* ] $t) => `(by
  solve
    | simp [$h,*]; exact $t
    | have lem := $t; simp [$h,*] at lem; simp [$h,*]; exact lem
    | exact ($t |> cast (by simp [$h,*])))

syntax (name := norm_subst_mod) "norm_subst%"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? term : term

macro_rules
| `(norm_subst% $t) => `(by
  solve
    | norm_subst; exact $t
    | have lem := $t; norm_subst at lem; norm_subst; exact lem
    | exact ($t |> cast (by norm_subst)))
| `(norm_subst% [ $h,* ] $t) => `(by
  solve
    | norm_subst [$h,*]; exact $t
    | have lem := $t; norm_subst [$h,*] at lem; norm_subst [$h,*]; exact lem
    | exact ($t |> cast (by norm_subst [$h,*])))

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
      | try simp [*]; try norm_subst
      | repeat (cases r; case' _ r => try rfl)
        try simp [*]; try norm_subst
      | repeat (cases r; case' _ r => try rfl)
        try simp [*]; try congr
})

macro "subst_solve_compose" : tactic => `(tactic| {
  intro s a b
  induction s generalizing a b
  all_goals simp [*]; try rfl
  all_goals
    repeat (cases a; case' _ a => try rfl)
    repeat (cases b; case' _ b => try rfl)
    try simp [*]
})
