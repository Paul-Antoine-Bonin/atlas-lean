module

public import MathlibExt.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR

namespace MetaMathlibExt.ULDMotzkin

private def ones : Fin 1 → ℕ := fun _ => 1

example : uldMotzkinNumber 1 ones 1 ones (by decide) 0 = 1 := by decide
example : uldMotzkinNumber 1 ones 1 ones (by decide) 2 = 2 := by decide

end MetaMathlibExt.ULDMotzkin
