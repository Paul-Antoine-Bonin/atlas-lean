/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.WeightedAffinePowerSum

namespace MetaMathlibExt

example : weightedAffinePowerSum (R := ℤ) 1 0 1 3 1 = 6 := by
  norm_num [weightedAffinePowerSum, Finset.sum_range_succ]

example (a b : ℤ) (u : ℤ) : weightedAffinePowerSum a b u 0 0 = 1 := by
  simp [weightedAffinePowerSum]

end MetaMathlibExt
