/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BNomialCoefficient
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

open Polynomial

namespace MetaMathlibExt

example : bNomialBase 3 (by decide) = (1 + X + X ^ 2 : Polynomial ℤ) := by
  norm_num [bNomialBase, Finset.sum_range_succ]

example : bNomialCoefficient 2 (by decide) 0 0 = 1 := by
  norm_num [bNomialCoefficient, bNomialBase, Finset.sum_range_succ, Polynomial.coeff_one]

example : bNomialCoefficient 2 (by decide) 2 (-1) = 0 := by
  simp [bNomialCoefficient]

example : bNomialCoefficient 3 (by decide) 2 2 = 3 := by
  norm_num [bNomialCoefficient, bNomialBase, Finset.sum_range_succ]
  ring_nf
  norm_num [Int.toNat, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

#print axioms MetaMathlibExt.bNomialBase
#print axioms MetaMathlibExt.bNomialCoefficient

end MetaMathlibExt

end
