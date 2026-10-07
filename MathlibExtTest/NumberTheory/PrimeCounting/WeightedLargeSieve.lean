/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.WeightedLargeSieve
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.NumberTheory.PrimeCounting.WeightedLargeSieve

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Apply the weighted large sieve to two points and constant coefficients at length two.
example :
    let x : Fin 2 → ℝ := ![0, 1 / 2]
    let δ : Fin 2 → ℝ := fun _ ↦ 1 / 2
    let a : ℕ → ℂ := fun _ ↦ 1
    ∑ r, (2 + 3 / (2 * δ r))⁻¹ *
        ‖∑ n ∈ Finset.range 2, a n *
          Complex.exp (((2 * Real.pi * (n * x r) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ n ∈ Finset.range 2, ‖a n‖ ^ 2 := by
  dsimp only
  apply weightedLargeSieve
  · intro r
    norm_num
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact (hrs rfl).elim
    · norm_num [AddCircle.norm_eq]
    · norm_num [AddCircle.norm_eq]
    · exact (hrs rfl).elim

end MathlibExtTest.NumberTheory.PrimeCounting.WeightedLargeSieve
