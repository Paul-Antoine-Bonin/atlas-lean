module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.FallingKBinomialTransform

namespace MetaMathlibExt

example : fallingKBinomialTransform 2 (fun n => n) 2 = 6 := by
  norm_num [fallingKBinomialTransform, Finset.sum_range_succ]

example : binomialTransform (fun n => n) 2 = 4 := by
  norm_num [binomialTransform, fallingKBinomialTransform, Finset.sum_range_succ]

end MetaMathlibExt
