module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.MeromorphicStirlingNumber

namespace MetaMathlibExt

example : meromorphicStirlingFirst 3 2 = -3 := by
  norm_num [meromorphicStirlingFirst, Nat.factorial]

example : besselNumberFirst 3 2 = -3 := by
  norm_num [besselNumberFirst, Nat.factorial]

example : meromorphicStirlingSecond 3 2 = 3 := by
  norm_num [meromorphicStirlingSecond, Nat.factorial]

example : besselNumberSecond 3 2 = 3 := by
  norm_num [besselNumberSecond, Nat.factorial]

end MetaMathlibExt
