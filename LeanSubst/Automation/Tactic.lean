
macro "lsimp " t:term : term => `(by
  solve
    | simp; exact $t
    | have lem := $t; simp at lem; simp; exact lem
    | exact ($t |> cast (by simp))
)

macro "subst_solve_id" : tactic => `(tactic| {
  intro s; induction s
  all_goals
    simp [*]
})

macro "subst_solve_stable" : tactic => `(tactic| {
  intro r σ h
  funext; case _ t =>
  induction t generalizing r σ
  all_goals
    try solve | subst h; simp [*] at *; try congr
    try solve | simp [*] at *
    try solve | subst h; simp [*]; rw [Subst.apply_stable]; congr
    try solve | {
      subst h; simp [*] at *
      rcases r with ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
      try simp [RenVec.to]
      try rw [Subst.apply_stable]; congr
    }
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
