module

public meta import Lean.Meta.Tactic.Simp

open Lean.Parser.Tactic

register_simp_attr subst_to
register_simp_attr subst_data

syntax (name := lsubst) "lsubst"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

macro_rules
| `(tactic| lsubst) => `(tactic| simp [subst_data])
| `(tactic| lsubst at $h) => `(tactic| simp [subst_data] at $h)
| `(tactic| lsubst [ $h,* ]) => `(tactic| simp [subst_data, $h,*])
| `(tactic| lsubst [ $h1,* ] at $h2) => `(tactic| simp [subst_data, $h1,*] at $h2)

syntax (name := lsubstup) "lsubstup"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

macro_rules
| `(tactic| lsubstup) => `(tactic| simp only [subst_to, <-subst_data])
| `(tactic| lsubstup at $h) => `(tactic| simp only [subst_to, <-subst_data] at $h)
| `(tactic| lsubstup [ $h,* ]) => `(tactic| simp only [subst_to, <-subst_data, $h,*])
| `(tactic| lsubstup [ $h1,* ] at $h2) => `(tactic| simp only [subst_to, <-subst_data, $h1,*] at $h2)

syntax (name := lsubst_mod) "lsubst%"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? term : term

macro_rules
| `(lsubst% $t) => `(by
  solve
    | lsubst; exact $t
    | have lem := $t; lsubst at lem; lsubst; exact lem
    | exact ($t |> cast (by lsubst)))
| `(lsubst% [ $h,* ] $t) => `(by
  solve
    | lsubst [$h,*]; exact $t
    | have lem := $t; lsubst [$h,*] at lem; lsubst [$h,*]; exact lem
    | exact ($t |> cast (by lsubst [$h,*])))

syntax (name := lsubstup_mod) "lsubstup%"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? term : term

macro_rules
| `(lsubstup% $t) => `(by
  solve
    | lsubstup; exact $t
    | have lem := $t; lsubstup at lem; lsubstup; exact lem
    | exact ($t |> cast (by lsubstup)))
| `(lsubstup% [ $h,* ] $t) => `(by
  solve
    | lsubstup [$h,*]; exact $t
    | have lem := $t; lsubstup [$h,*] at lem; lsubstup [$h,*]; exact lem
    | exact ($t |> cast (by lsubstup [$h,*])))

macro "subst_solve_id" : tactic => `(tactic| {
  intro s; induction s
  all_goals
    lsubst [*]
})

macro "subst_solve_stable" : tactic => `(tactic| {
  intro r σ h; subst h
  funext; case _ t =>
  induction t generalizing r
  all_goals
    solve
      | try lsubst [*]; try lsubstup
      | repeat (cases r; case' _ r => try rfl)
        try lsubst [*]; try lsubstup
      | repeat (cases r; case' _ r => try rfl)
        try lsubst [*]; try congr
})

macro "subst_solve_compose" : tactic => `(tactic| {
  intro s a b
  induction s generalizing a b
  all_goals lsubst [*]; try rfl
  all_goals
    repeat (cases a; case' _ a => try rfl)
    repeat (cases b; case' _ b => try rfl)
    try lsubst [*]
})
