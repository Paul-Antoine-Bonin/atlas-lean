/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.Coeff
public import MathlibExt.RingTheory.Polynomial.MorganVoycePolynomial

namespace MetaMathlibExt

example : morganVoyceCoeff 3 2 = 5 := by decide
example : morganVoyceCoeff 2 3 = 0 := by decide

example : (morganVoycePolynomial ℤ 3).coeff 2 = 5 := by
  norm_num [morganVoycePolynomial, morganVoyceCoeff, Finset.sum_range_succ]
  simp [Polynomial.coeff_one]

end MetaMathlibExt
