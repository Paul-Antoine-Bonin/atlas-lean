/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RiordanNumber
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : riordanNumber 0 = 1 := by
  norm_num [riordanNumber, catalan_zero, Finset.sum_range_succ_comm]

example : riordanNumber 2 = 1 := by
  norm_num [riordanNumber, catalan_zero, catalan_one, catalan_two,
    Finset.sum_range_succ_comm]

end MetaMathlibExt
