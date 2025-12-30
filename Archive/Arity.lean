import LeanSubst.Basic

namespace LeanSubst

variable {T : Type}

def mk0 : Fin 0 -> T
| x => nomatch x

@[simp]
theorem mk0_eta {t : Fin 0 -> T} : t = mk0 := by
  funext; case _ x =>
  cases x; case _ x p =>
  cases p

def mk1 : T -> Fin 1 -> T
| t, .mk 0 _ => t

@[simp]
theorem mk1_eta {t : Fin 1 -> T} : (λ i => (mk1 (t 0)) i) = t := by
  funext; case _ x =>
  cases x; case _ x p =>
  cases x; simp [mk1]
  omega

@[simp]
theorem mk1_0 {t : T} : mk1 t 0 = t := by simp [mk1]

@[simp]
theorem mk1_cong {a1 a2 : T} : mk1 a1 = mk1 a2 <-> a1 = a2 := by
  apply Iff.intro
  case _ =>
    intro h
    have lem : ∀ x, mk1 a1 x = mk1 a2 x := by rw [h]; simp
    replace lem := lem 0; simp at lem
    apply lem
  case _ => intro h; subst h; rfl

def mk2 : T -> T -> Fin 2 -> T
| t1, _, .mk 0 _ => t1
| _, t2, .mk 1 _ => t2

@[simp]
theorem mk2_eta {t : Fin 2 -> T} : (λ i => (mk2 (t 0) (t 1)) i) = t := by
  funext; case _ x =>
  cases x; case _ x p =>
  cases x; simp [mk2]; case _ x =>
  cases x; simp [mk2]
  omega

@[simp]
theorem mk2_0 {t1 t2 : T} : mk2 t1 t2 0 = t1 := by simp [mk2]

@[simp]
theorem mk2_1 {t1 t2 : T} : mk2 t1 t2 1 = t2 := by simp [mk2]

@[simp]
theorem mk2_cong {a1 b1 a2 b2 : T} : mk2 a1 b1 = mk2 a2 b2 <-> a1 = a2 ∧ b1 = b2 := by
  apply Iff.intro
  case _ =>
    intro h
    have lem : ∀ x, mk2 a1 b1 x = mk2 a2 b2 x := by rw [h]; simp
    have lem1 := lem 0; simp at lem1; subst lem1
    have lem2 := lem 1; simp at lem2; subst lem2
    simp
  case _ => intro h; rw [h.1, h.2]

def mk3 : T -> T -> T -> Fin 3 -> T
| t1, _, _, .mk 0 _ => t1
| _, t2, _, .mk 1 _ => t2
| _, _, t3, .mk 2 _ => t3

@[simp]
theorem mk3_eta {t : Fin 3 -> T} : (λ i => (mk3 (t 0) (t 1) (t 2)) i) = t := by
  funext; case _ x =>
  cases x; case _ x p =>
  cases x; simp [mk3]; case _ x =>
  cases x; simp [mk3]; case _ x =>
  cases x; simp [mk3]
  omega

@[simp]
theorem mk3_0 {t1 t2 t3 : T} : mk3 t1 t2 t3 0 = t1 := by simp [mk3]

@[simp]
theorem mk3_1 {t1 t2 t3 : T} : mk3 t1 t2 t3 1 = t2 := by simp [mk3]

@[simp]
theorem mk3_2 {t1 t2 t3 : T} : mk3 t1 t2 t3 2 = t3 := by simp [mk3]

@[simp]
theorem mk3_cong {a1 b1 c1 a2 b2 c2 : T}
  : mk3 a1 b1 c1 = mk3 a2 b2 c2 <-> a1 = a2 ∧ b1 = b2 ∧ c1 = c2
:= by
  apply Iff.intro
  case _ =>
    intro h
    have lem : ∀ x, mk3 a1 b1 c1 x = mk3 a2 b2 c2 x := by rw [h]; simp
    have lem1 := lem 0; simp at lem1; subst lem1
    have lem2 := lem 1; simp at lem2; subst lem2
    have lem3 := lem 2; simp at lem3; subst lem3
    simp
  case _ => intro h; rw [h.1, h.2.1, h.2.2]

def mk4 : T -> T -> T -> T -> Fin 4 -> T
| t1, _, _, _, .mk 0 _ => t1
| _, t2, _, _, .mk 1 _ => t2
| _, _, t3, _, .mk 2 _ => t3
| _, _, _, t4, .mk 3 _ => t4

@[simp]
theorem mk4_eta {t : Fin 4 -> T} : (λ i => (mk4 (t 0) (t 1) (t 2) (t 3)) i) = t := by
  funext; case _ x =>
  cases x; case _ x p =>
  cases x; simp [mk4]; case _ x =>
  cases x; simp [mk4]; case _ x =>
  cases x; simp [mk4]; case _ x =>
  cases x; simp [mk4]
  omega

@[simp]
theorem mk4_0 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 0 = t1 := by simp [mk4]

@[simp]
theorem mk4_1 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 1 = t2 := by simp [mk4]

@[simp]
theorem mk4_2 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 2 = t3 := by simp [mk4]

@[simp]
theorem mk4_3 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 3 = t4 := by simp [mk4]

@[simp]
theorem mk4_cong {a1 b1 c1 d1 a2 b2 c2 d2 : T}
  : mk4 a1 b1 c1 d1 = mk4 a2 b2 c2 d2 <-> a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2
:= by
  apply Iff.intro
  case _ =>
    intro h
    have lem : ∀ x, mk4 a1 b1 c1 d1 x = mk4 a2 b2 c2 d2 x := by rw [h]; simp
    have lem1 := lem 0; simp at lem1; subst lem1
    have lem2 := lem 1; simp at lem2; subst lem2
    have lem3 := lem 2; simp at lem3; subst lem3
    have lem4 := lem 3; simp at lem4; subst lem4
    simp
  case _ => intro h; rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

section

  variable [RenMap T] [SubstMap T T]

  @[simp]
  theorem subst_mk0 {σ : Subst T} {x} : (mk0 x)[σ:T] = mk0 x := by
    cases x; case _ x p =>
    cases p

  @[simp]
  theorem subst_mk1 {σ : Subst T} {t : T} {x} : (mk1 t x)[σ] = mk1 t[σ] x := by
    cases x; case _ x p =>
    cases x; simp
    case succ => simp at p

  @[simp]
  theorem subst_mk2 {σ : Subst T} {t1 t2 : T} {x} : (mk2 t1 t2 x)[σ] = mk2 t1[σ] t2[σ] x := by
    cases x; case _ x p =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    omega

  @[simp]
  theorem subst_mk3 {σ : Subst T} {t1 t2 t3 : T} {x}
    : (mk3 t1 t2 t3 x)[σ] = mk3 t1[σ] t2[σ] t3[σ] x
  := by
    cases x; case _ x p =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    omega

  @[simp]
  theorem subst_mk4 {σ : Subst T} {t1 t2 t3 t4 : T} {x}
    : (mk4 t1 t2 t3 t4 x)[σ] = mk4 t1[σ] t2[σ] t3[σ] t4[σ] x
  := by
    cases x; case _ x p =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    omega

end

end LeanSubst
