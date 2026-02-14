
inductive Ty where
| base : Ty
| arrow : Ty -> Ty -> Ty

notation "★" => Ty.base
infixr:78 " -:> " => Ty.arrow

inductive Var : List Ty -> Ty -> Type where
| here {Γ A} : Var (A::Γ) A
| there {Γ A B} : Var Γ B -> Var (A::Γ) B

inductive Term : List Ty -> Ty -> Type where
| var {Γ T} :
  Var Γ T ->
  Term Γ T
| lam {Γ A B} :
  Term (A::Γ) B ->
  Term Γ (A -:> B)
| app {Γ A B} :
  Term Γ (A -:> B) ->
  Term Γ A ->
  Term Γ B

def Ren (Γ Δ : List Ty) := ∀ {T}, Var Γ T -> Var Δ T

def Ren.lift {Γ Δ : List Ty} (r : Ren Γ Δ) {T : Ty} : Ren (T::Γ) (T::Δ)
| _, .here => .here
| _, .there x => .there (r x)

def Term.rmap {Γ Δ : List Ty} (r : Ren Γ Δ) {T : Ty} : Term Γ T -> Term Δ T
| var v => var (r v)
| lam t => lam (rmap (Ren.lift r) t)
| app f a => app (rmap r f) (rmap r a)

inductive Action (Γ : List Ty) (T : Ty) : Type where
| re : Var Γ T -> Action Γ T
| su : Term Γ T -> Action Γ T

def Subst (Γ Δ : List Ty) := ∀ {T}, Var Γ T -> Action Δ T

def Subst.lift {Γ Δ : List Ty} (σ : Subst Γ Δ) {T : Ty} : Subst (T::Γ) (T::Δ)
| _, .here => .re .here
| _, .there x =>
  match σ x with
  | .su t => .su (Term.rmap .there t)
  | .re k => .re (.there k)

def Term.smap {Γ Δ : List Ty} (σ : Subst Γ Δ) {T : Ty} : Term Γ T -> Term Δ T
| var v =>
  match σ v with
  | .su t => t
  | .re k => var k
| lam t => lam (smap (Subst.lift σ) t)
| app f a => app (smap σ f) (smap σ a)
