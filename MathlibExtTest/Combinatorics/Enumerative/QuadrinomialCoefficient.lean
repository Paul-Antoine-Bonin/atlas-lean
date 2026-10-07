/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Coeff
public import MathlibExt.Combinatorics.Enumerative.QuadrinomialCoefficient

namespace MetaMathlibExt

example : polynomialQuadrinomialCoeff 1 0 = 1 := by
  simp [polynomialQuadrinomialCoeff]

example : polynomialQuadrinomialCoeff 1 2 = 1 := by
  simp [polynomialQuadrinomialCoeff, Polynomial.coeff_one, Polynomial.coeff_X]

end MetaMathlibExt
