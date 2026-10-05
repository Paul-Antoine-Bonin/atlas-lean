module

public import MathlibExt.Combinatorics.Enumerative.PentagonalNumber

namespace MetaMathlibExt

example : partitionFunction 0 = 1 := by simp

example : partitionFunction 1 = 1 := by simp

example (n : ℕ) : partitionFunction n = Fintype.card (Nat.Partition n) := rfl

end MetaMathlibExt
