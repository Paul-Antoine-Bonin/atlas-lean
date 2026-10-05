module

public import MathlibExt.Combinatorics.Enumerative.SmarandachePermutationSequence

namespace MetaMathlibExt

example : smarandacheBlock 4 = [1, 3, 5, 7, 8, 6, 4, 2] := by rfl
example : List.map smarandachePermutation (List.range 6) = [1, 2, 1, 3, 4, 2] := by rfl

end MetaMathlibExt
