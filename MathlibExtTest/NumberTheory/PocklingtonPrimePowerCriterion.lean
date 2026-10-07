/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PocklingtonPrimePowerCriterion
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Prime

-- The witness `a = 2` certifies `13 = 3 * 2 ^ 2 + 1`.
example : Nat.Prime 13 := by
  apply MetaMathlibExt.pocklington_prime_power_criterion 13 3 2 2
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine ⟨2, ?_, ?_⟩
    · norm_num
    · norm_num

-- The witness `a = 5` certifies `97 = 3 * 2 ^ 5 + 1`.
example : Nat.Prime 97 := by
  apply MetaMathlibExt.pocklington_prime_power_criterion 97 3 2 5
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine ⟨5, ?_, ?_⟩
    · norm_num
    · norm_num
