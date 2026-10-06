module

public import MathlibExt.Combinatorics.Enumerative.DombNumber

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

example : dombNumber 0 = 1 := rfl

example : dombNumber 1 = 4 := rfl

example : dombNumber 2 = 28 := rfl

example (n : ℕ) :
    dombNumber n =
      ∑ k ∈ Finset.range (n + 1),
        n.choose k ^ 2 * (2 * k).choose k * (2 * (n - k)).choose (n - k) :=
  dombNumber_unfold n

end

end MetaMathlibExt
