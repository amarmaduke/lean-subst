
namespace LeanSubst

  universe u
  variable {T : Type u} {F : Type u -> Type u} [Monad F]

  @[simp]
  def join (xs : F (F T)) : F T := bind xs id

  variable [LawfulMonad F]

  @[simp]
  theorem join_pure_id {x : F T} : join (pure (f := F) x) = x := by simp [join]

end LeanSubst
