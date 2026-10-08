/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.BesselPolynomial

namespace MetaMathlibExt

example : besselPolynomial 0 = 1 := besselPolynomial_zero

example :
    besselPolynomial 2 =
      Polynomial.C 1 + Polynomial.C 3 * Polynomial.X +
        Polynomial.C 3 * Polynomial.X ^ 2 :=
  besselPolynomial_two

end MetaMathlibExt
