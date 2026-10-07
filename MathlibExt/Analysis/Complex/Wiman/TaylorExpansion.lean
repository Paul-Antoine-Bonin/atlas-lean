/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section

namespace Complex

noncomputable section

/-- An entire function is the sum of the Taylor coefficients used by the Wiman definitions. -/
theorem hasSum_wimanTaylorCoefficient_mul_pow
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n : ℕ => wimanTaylorCoefficient f n * z ^ n) (f z) := by
  simpa only [sub_zero, smul_eq_mul, wimanTaylorCoefficient, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasSum_taylorSeries_of_entire hf 0 z)

end

end Complex
