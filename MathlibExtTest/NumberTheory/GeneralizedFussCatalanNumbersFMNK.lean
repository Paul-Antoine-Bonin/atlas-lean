/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK

namespace MetaMathlibExt

example : generalizedFussCatalanNumber 2 3 1 = 5 := by decide

example : generalizedFussCatalanNumber 3 2 1 = 3 := by decide

example : generalizedFussCatalanNumber 7 1 4 = 4 := by decide

example : generalizedFussCatalanNumber 2 0 1 = 1 := by decide

example (m k : ℕ) : generalizedFussCatalanNumber m 1 k = k :=
  generalizedFussCatalanNumber_one m k

end MetaMathlibExt
