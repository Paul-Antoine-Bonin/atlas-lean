/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
