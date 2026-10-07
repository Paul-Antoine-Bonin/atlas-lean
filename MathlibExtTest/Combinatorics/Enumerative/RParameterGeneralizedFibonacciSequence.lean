/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.Combinatorics.Enumerative.RParameterGeneralizedFibonacciSequence

namespace MetaMathlibExt

example (r : ℝ) : rFibonacciNumber r 0 = 1 := by
  simp [rFibonacciNumber]

example (r : ℝ) : rFibonacciNumber r 3 = 1 + 2 * r := by
  simp [rFibonacciNumber, Finset.sum_range_succ]

end MetaMathlibExt
