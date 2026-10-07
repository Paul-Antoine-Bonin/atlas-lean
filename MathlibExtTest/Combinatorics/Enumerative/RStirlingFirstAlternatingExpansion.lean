/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion

namespace MetaMathlibExt

example : rStirlingFirst 2 2 2 = 1 := by simp [rStirlingFirst_self]

example : rStirlingFirst 2 1 2 = 0 := by simp [rStirlingFirst_self]

example : rStirlingFirst 5 0 2 = 0 := rStirlingFirst_zero_of_pos 5 2 (by omega)

example : rStirlingFirst 3 2 2 = 2 := by
  rw [rStirlingFirst_succ 2 2 2 (by omega) le_rfl]
  simp [rStirlingFirst_self]

end MetaMathlibExt
