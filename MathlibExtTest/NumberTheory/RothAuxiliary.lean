/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RothAuxiliary
import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

namespace MathlibExtTest.NumberTheory.RothAuxiliary

open MathlibExt.NumberTheory.RothAuxiliary

-- The shared theorem handles a positive numerator-divisibility weight at the prime `2`.
example : Set.Finite {q : ℚ |
    |Real.sqrt 2 - (q : ℝ)| <
        1 / Real.rpow (q.den : ℝ) (9 / 4 : ℝ) ∧
      ∃ a : ℕ,
        ((2 ^ a : ℕ) : ℤ) ∣ q.num ∧
          Real.rpow (q.den : ℝ) (1 / 4 : ℝ) ≤ (2 : ℝ) ^ a} := by
  have hsqrt : IsAlgebraic ℚ (Real.sqrt 2) := by
    apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcore := finite_of_divisible_approximations
    (Real.sqrt 2) hsqrt
    (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ ↦ 2)
    (fun _ ↦ (1 / 4 : ℝ)) (fun _ ↦ 0)
    (by simp) (by simp) (by norm_num)
  refine hcore.subset ?_
  intro q hq
  rcases hq with ⟨happrox, a, hdiv, hlarge⟩
  refine ⟨?_, (fun _ ↦ a), (fun _ ↦ 0), ?_⟩
  · norm_num at happrox ⊢
    exact happrox
  · refine ⟨?_, by simp, ?_⟩
    · simpa using hdiv
    · intro l hl
      refine ⟨?_, by norm_num⟩
      simpa using hlarge

end MathlibExtTest.NumberTheory.RothAuxiliary
