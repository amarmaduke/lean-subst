
macro "subst_solve_id" : tactic => `(tactic| {
  intro s; induction s
  all_goals
    try solve | simp [*] at *
  -- intro t; induction t
  -- any_goals solve | simp_all +instances
  -- all_goals try simp at *; simp  +instances [*]; grind
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
  intro s σ τ
  let T := Subst.typeof s
  induction s generalizing σ τ
  all_goals try solve | simp [*]
  all_goals try solve |
    try rcases σ with ⟨σ1, σ2, σ3, σ4, σ5, σ6, σ7, σ8⟩
    try rcases τ with ⟨τ1, τ2, τ3, τ4, τ5, τ6, τ7, τ8⟩
    try simp [Subst.rewrite_lift_compose (T := T), *]
    try simp [Subst.lift_compose_ren_right (T := T), *]
    try simp [Subst.rewrite_lift_compose_ren_left (T := T), *]
    try solve | congr
    try solve | congr 1
    try solve | congr 2
    try solve | grind
  all_goals solve | simp; grind
})
