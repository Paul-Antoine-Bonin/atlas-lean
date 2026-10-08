/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RearickLogarithm

namespace MetaMathlibExt

example (f : ArithmeticFunction ℝ) (hf : 0 < f 1) : rearickLog f hf 0 = 0 := by simp

example (f : ArithmeticFunction ℝ) (hf : 0 < f 1) (h1 : f 1 = 1) : rearickLog f hf 1 = 0 := by
  simp [h1]

example (f : ArithmeticFunction ℝ) (hf : 0 < f 1) :
    rearickLog f hf 2 = ∑ d ∈ (2 : ℕ).divisors,
      f d * ArithmeticFunction.dirichletInverse (⇑f) (invertibleOfNonzero (ne_of_gt hf)) (2 / d) *
        Real.log (d : ℝ) :=
  rearickLog_apply_of_one_lt f hf one_lt_two

example (f : ArithmeticFunction ℝ) (hf : 0 < f 1) (h1 : f 1 = 1) :
    rearickLog f hf * f = f.pmul ArithmeticFunction.log := by
  rw [rearickLog_eq_pmul_log_mul_dirichletInverse f hf h1, mul_assoc,
    ArithmeticFunction.dirichletInverse_mul_self, mul_one]

example (f : ArithmeticFunction ℝ) (hf : 0 < f 1) (hmult : f.IsMultiplicative) :
    rearickLog f hf 6 = 0 :=
  (rearick_log_eq_zero_iff_isMultiplicative f hf).1 hmult 6 (by decide)

end MetaMathlibExt
