/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.Enumerative.CatalanLarcombeFrenchNumber

namespace MetaMathlibExt

example : catalanLarcombeFrenchNumber 0 = 1 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

example : catalanLarcombeFrenchNumber 1 = 8 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

example : catalanLarcombeFrenchNumber 2 = 80 := by
  norm_num [catalanLarcombeFrenchNumber, Finset.sum_range_succ, Nat.choose]

end MetaMathlibExt
