/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ThueSiegelRoth
import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

namespace MathlibExtTest.NumberTheory.ThueSiegelRoth

open MathlibExt.NumberTheory.ThueSiegelRothWanted

-- Roth's theorem applies to `√2` with exponent `2 + 1/2`.
example : Set.Finite {q : ℚ |
    |Real.sqrt 2 - (q : ℝ)| <
      1 / Real.rpow (q.den : ℝ) (2 + (1 / 2 : ℝ))} := by
  apply thue_siegel_roth (Real.sqrt 2)
  · apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · exact irrational_sqrt_two
  · norm_num

end MathlibExtTest.NumberTheory.ThueSiegelRoth
