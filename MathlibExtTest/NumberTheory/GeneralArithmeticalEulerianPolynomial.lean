/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralArithmeticalEulerianPolynomial
import Mathlib.Tactic

namespace MetaMathlibExt

open Polynomial

example : generalArithmeticalEulerianNumber ℤ 2 0 0 1 = 1 := by
  norm_num [generalArithmeticalEulerianNumber, Finset.sum_range_succ]

example : generalArithmeticalEulerianNumber ℤ 2 1 0 1 = 1 := by
  norm_num [generalArithmeticalEulerianNumber, Finset.sum_range_succ]

example : generalArithmeticalEulerianPolynomial ℤ 2 0 1 = 1 + X := by
  norm_num [generalArithmeticalEulerianPolynomial, generalArithmeticalEulerianNumber,
    Finset.sum_range_succ]

#print axioms generalArithmeticalEulerianNumber
#print axioms generalArithmeticalEulerianPolynomial

end MetaMathlibExt
