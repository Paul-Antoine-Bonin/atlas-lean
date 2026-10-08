/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.QuadrinomialCoefficients

namespace MetaMathlibExt

example : quadrinomialCoeff 0 = 1 := by decide
example : quadrinomialCoeff 1 = 1 := by decide
example : quadrinomialCoeff 2 = 3 := by decide
example : quadrinomialCoeff 3 = 10 := by decide

example (n : ℕ) : quadrinomialCoeff n = zhangVSum n 1 1 0 0 0 :=
  quadrinomialCoeff_eq_zhangVSum n

#print axioms zhangVSum
#print axioms quadrinomialCoeff
#print axioms quadrinomialCoeff_eq_zhangVSum

end MetaMathlibExt
