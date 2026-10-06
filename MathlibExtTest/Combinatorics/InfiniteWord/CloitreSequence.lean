module

public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence

namespace MetaMathlibExt

example : cloitreApprox 2 = [1, 1, 2, 1, 1, 1, 1] := by decide

example : (List.range 15).map cloitreSequence =
    [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2] := by
  decide

end MetaMathlibExt
