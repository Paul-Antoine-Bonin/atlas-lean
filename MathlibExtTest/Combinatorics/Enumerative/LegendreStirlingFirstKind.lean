/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : legendreStirlingFirst 0 0 = 1 := by
  norm_num [legendreStirlingFirst_zero]

example : legendreStirlingFirst 3 4 = 0 :=
  legendreStirlingFirst_eq_zero_of_lt 3 4 (by decide)

example : legendreStirlingFirst 4 4 = 1 :=
  legendreStirlingFirst_diag 4

private theorem legendreStirlingFirst_two_zero : legendreStirlingFirst 2 0 = 0 := by
  norm_num [legendreStirlingFirst, jacobiStirlingFirst, jacobiStirlingFirstPoly,
    Finset.prod_range_succ, Polynomial.coeff_mul]

private theorem legendreStirlingFirst_two_one : legendreStirlingFirst 2 1 = -2 := by
  rw [legendreStirlingFirst_succ 1 0]
  have h10 : legendreStirlingFirst 1 0 = 0 := by
    norm_num [legendreStirlingFirst, jacobiStirlingFirst, jacobiStirlingFirstPoly,
      Finset.prod_range_succ, Polynomial.coeff_mul]
  rw [h10, legendreStirlingFirst_diag]
  norm_num

example : legendreStirlingFirst 3 1 = 12 := by
  rw [legendreStirlingFirst_succ 2 0, legendreStirlingFirst_two_zero,
    legendreStirlingFirst_two_one]
  norm_num

example : legendreStirlingFirst 3 2 = -8 := by
  rw [legendreStirlingFirst_succ 2 1, legendreStirlingFirst_two_one,
    legendreStirlingFirst_diag]
  norm_num

end MetaMathlibExt
