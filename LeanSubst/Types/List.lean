
import LeanSubst.Lemma
import LeanSubst.Types.Option

namespace LeanSubst

universe u1 u2 u3
variable {S : Type u1} {T T1 T2 : Type u2} {U : Type u3}
variable {V : List (Type u2)}

@[simp]
theorem List.rmap_append [RenMap S V] {xs ys : List S} {r : RenVec V}
  : (xs ++ ys)⟨r,⟩ = xs⟨r,⟩ ++ ys⟨r,⟩
:= by induction xs generalizing ys <;> simp [*]

@[simp]
theorem List.smap_append [SubstMap S V] {xs ys : List S} {σ : SubstVec V}
  : (xs ++ ys)[σ,] = xs[σ,] ++ ys[σ,]
:= by induction xs generalizing ys <;> simp [*]

@[simp]
theorem List.rmap_get? [RenMap S V] {x : List S} {n : Nat} {r : RenVec V}
  : x[n]?⟨r,⟩ = x⟨r,⟩[n]?
:= by
  induction x generalizing n r <;> simp [*]
  case cons => cases n <;> simp [*]
@[simp]
theorem List.smap_get? [SubstMap S V] {x : List S} {n : Nat} {σ : SubstVec V}
  : x[n]?[σ,] = x[σ,][n]?
:= by
  induction x generalizing n σ <;> simp [*]
  case cons => cases n <;> simp [*]

@[simp]
theorem List.rmap_length [RenMap S V] {x : List S} {r : RenVec V}
  : x⟨r,⟩.length = x.length
:= by induction x generalizing r <;> simp [*]

@[simp]
theorem List.smap_length [SubstMap S V] {x : List S} {σ : SubstVec V}
  : x[σ,].length = x.length
:= by induction x generalizing σ <;> simp [*]

@[simp]
theorem List.rmap_reverse [RenMap S V] {x : List S} {r : RenVec V}
  : x.reverse⟨r,⟩ = x⟨r,⟩.reverse
:= by induction x generalizing r <;> simp [*]

@[simp]
theorem List.smap_reverse [SubstMap S V] {x : List S} {σ : SubstVec V}
  : x.reverse[σ,] = x[σ,].reverse
:= by induction x generalizing σ <;> simp [*]

@[simp]
theorem List.rmap_map_su [RenMap T (T::V)] {x : List T} {r : RenVec (T::V)}
  : (x.map su)⟨r,⟩ = x⟨r,⟩.map su
:= by induction x generalizing r <;> simp [*]

@[simp]
theorem List.smap_map_su [SubstMap T (T::V)] {x : List T} {σ : SubstVec (T::V)}
  : (x.map su)[σ,] = x[σ,].map su
:= by induction x generalizing σ <;> simp [*]

end LeanSubst
