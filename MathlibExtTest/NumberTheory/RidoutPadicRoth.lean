/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RidoutPadicRoth
import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

namespace MathlibExtTest.NumberTheory.RidoutPadicRoth

theorem sqrt_two_isAlgebraic : IsAlgebraic ℚ (Real.sqrt 2) := by
  apply IsIntegral.isAlgebraic
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
    Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

-- Ridout's theorem applies to `√2`, exponent `5/2`, and the prime `2`.
example : Set.Finite {r : ℚ |
    ((∏ l ∈ ({⟨2, Nat.prime_two⟩} : Finset Nat.Primes),
      padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
        |Real.sqrt 2 - (r : ℝ)| <
      (((max r.num.natAbs r.den : ℕ) : ℝ) ^ (2 + (1 / 2 : ℝ)))⁻¹} := by
  apply MetaMathlibExt.ridout_padic_roth (Real.sqrt 2)
  · exact sqrt_two_isAlgebraic
  · exact irrational_sqrt_two
  · norm_num

end MathlibExtTest.NumberTheory.RidoutPadicRoth
