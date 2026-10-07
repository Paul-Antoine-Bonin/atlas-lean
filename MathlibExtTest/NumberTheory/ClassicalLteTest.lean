/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ClassicalLte
import Mathlib.Tactic

namespace MetaMathlibExt

example :
    padicValInt 3 ((4 : ℤ) ^ 2 - 1 ^ 2) =
      padicValNat 3 2 + padicValInt 3 ((4 : ℤ) - 1) := by
  apply padicValInt_pow_sub_pow
  · decide
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end MetaMathlibExt
