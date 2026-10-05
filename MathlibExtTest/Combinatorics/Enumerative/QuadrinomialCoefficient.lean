module

import Mathlib.Algebra.Polynomial.Coeff
public import MathlibExt.Combinatorics.Enumerative.QuadrinomialCoefficient

namespace MetaMathlibExt

example : polynomialQuadrinomialCoeff 1 0 = 1 := by
  simp [polynomialQuadrinomialCoeff]

example : polynomialQuadrinomialCoeff 1 2 = 1 := by
  simp [polynomialQuadrinomialCoeff, Polynomial.coeff_one, Polynomial.coeff_X]

end MetaMathlibExt
