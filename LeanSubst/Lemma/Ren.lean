
import LeanSubst.Ops

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T : Type u2}

class RenMapId (S : Type u1) [RenMap S] where
  apply_id {t : S} : t⟨Ren.id⟩ = t

class RenMapCompose (S : Type u1) [RenMap S] where
  apply_compose {s : S} {r1 r2 : Ren} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

@[simp]
theorem Ren.apply_id [RenMap T] [RenMapId T] {t : T} : t⟨id⟩ = t := RenMapId.apply_id

@[simp, grind =]
theorem Ren.apply_compose [RenMap T] [RenMapCompose T] {t : T} {r1 r2 : Ren}
  : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
:= RenMapCompose.apply_compose


end LeanSubst
