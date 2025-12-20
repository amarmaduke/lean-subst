import LeanSubst.Basic

namespace LeanSubst

variable {T : Type}

def mk0 : Fin 0 -> T
| x => nomatch x

def mk1 : T -> Fin 1 -> T
| t, .mk 0 _ => t

@[simp]
theorem mk1_0 {t : T} : mk1 t 0 = t := by simp [mk1]

def mk2 : T -> T -> Fin 2 -> T
| t1, _, .mk 0 _ => t1
| _, t2, .mk 1 _ => t2

@[simp]
theorem mk2_0 {t1 t2 : T} : mk2 t1 t2 0 = t1 := by simp [mk2]

@[simp]
theorem mk2_1 {t1 t2 : T} : mk2 t1 t2 1 = t2 := by simp [mk2]

def mk3 : T -> T -> T -> Fin 3 -> T
| t1, _, _, .mk 0 _ => t1
| _, t2, _, .mk 1 _ => t2
| _, _, t3, .mk 2 _ => t3

@[simp]
theorem mk3_0 {t1 t2 t3 : T} : mk3 t1 t2 t3 0 = t1 := by simp [mk3]

@[simp]
theorem mk3_1 {t1 t2 t3 : T} : mk3 t1 t2 t3 1 = t2 := by simp [mk3]

@[simp]
theorem mk3_2 {t1 t2 t3 : T} : mk3 t1 t2 t3 2 = t3 := by simp [mk3]

def mk4 : T -> T -> T -> T -> Fin 4 -> T
| t1, _, _, _, .mk 0 _ => t1
| _, t2, _, _, .mk 1 _ => t2
| _, _, t3, _, .mk 2 _ => t3
| _, _, _, t4, .mk 3 _ => t4

@[simp]
theorem mk4_0 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 0 = t1 := by simp [mk4]

@[simp]
theorem mk4_1 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 1 = t2 := by simp [mk4]

@[simp]
theorem mk4_2 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 2 = t3 := by simp [mk4]

@[simp]
theorem mk4_3 {t1 t2 t3 t4 : T} : mk4 t1 t2 t3 t4 3 = t4 := by simp [mk4]

section

  variable [SubstMap T]

  @[simp]
  theorem subst_mk0 {σ : Subst T} {x} : (mk0 x)[σ] = mk0 x := by
    cases x; case _ x p =>
    cases p

  @[simp]
  theorem subst_mk1 {σ : Subst T} {t x} : (mk1 t x)[σ] = mk1 t[σ] x := by
    cases x; case _ x p =>
    cases x; simp
    case succ => simp at p

  @[simp]
  theorem subst_mk2 {σ : Subst T} {t1 t2 x} : (mk2 t1 t2 x)[σ] = mk2 t1[σ] t2[σ] x := by
    cases x; case _ x p =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    omega

  @[simp]
  theorem subst_mk3 {σ : Subst T} {t1 t2 t3 x}
    : (mk3 t1 t2 t3 x)[σ] = mk3 t1[σ] t2[σ] t3[σ] x
  := by
    cases x; case _ x p =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    cases x; simp; case _ x =>
    omega

  @[simp]
  theorem subst_mk4 {σ : Subst T} {t1 t2 t3 t4 x}
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
