/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotientWeighted

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Specialize the weighted squarefree-totient lower bound at its endpoint.
example :
    Real.log 100 + 36 / 100 <
      ∑ q ∈ Finset.Icc 1 (100 : ℕ), (1 + (q : ℝ) / 100)⁻¹ *
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q) := by
  exact squarefreeTotientWeightedLower 100 (by norm_num)

end MathlibExtTest.NumberTheory.PrimeCounting.SquarefreeTotientWeighted
