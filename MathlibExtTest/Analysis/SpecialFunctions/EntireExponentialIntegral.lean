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
