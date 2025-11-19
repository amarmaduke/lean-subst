
namespace LeanSubst

  universe u

  class PrefixHash (T : Type u) where
    hash : Nat -> T

  prefix:max "#" => PrefixHash.hash

  class PrefixPercent (T : Type u) (F : Type u -> Type u) where
    percent : T -> F T

  prefix:max "%" => PrefixPercent.percent

end LeanSubst
