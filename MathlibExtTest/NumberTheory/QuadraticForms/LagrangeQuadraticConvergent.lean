/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.LagrangeQuadraticConvergent

namespace MetaMathlibExt

-- The solution `(u, y) = (0, 1)` for `u² + y² = 1` gives the zeroth convergent.
example :
    let ω : ℝ := -((0 : ℤ) : ℝ) / (2 * ((1 : ℤ) : ℝ))
    ∃ n : ℕ,
      (n = 0 ∨ ¬(GenContFract.of ω).TerminatedAt (n - 1)) ∧
        ((ω.convergent n : ℚ) : ℝ) = ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ) := by
  apply lagrange_quadratic_convergent (R := 1)
  all_goals norm_num

-- The solution `(u, y) = (-1, 2)` for `5u² + 6uy + 2y² = 1` covers discriminant `-4`.
example :
    let ω : ℝ := -((6 : ℤ) : ℝ) / (2 * ((5 : ℤ) : ℝ))
    ∃ n : ℕ,
      (n = 0 ∨ ¬(GenContFract.of ω).TerminatedAt (n - 1)) ∧
        ((ω.convergent n : ℚ) : ℝ) = ((-1 : ℤ) : ℝ) / ((2 : ℤ) : ℝ) := by
  apply lagrange_quadratic_convergent (R := 2)
  all_goals norm_num

end MetaMathlibExt
