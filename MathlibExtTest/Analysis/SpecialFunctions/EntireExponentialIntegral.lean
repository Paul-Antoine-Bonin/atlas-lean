/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.EntireExponentialIntegral

namespace Complex

example (z : ℂ) :
    HasDerivAt ein
      (∑' n : ℕ, (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z :=
  hasDerivAt_ein z

example (z : ℂ) : z * deriv ein z = 1 - exp (-z) :=
  mul_deriv_ein z

example : ein 0 = 0 := by
  simp [ein, einTerm]

end Complex
