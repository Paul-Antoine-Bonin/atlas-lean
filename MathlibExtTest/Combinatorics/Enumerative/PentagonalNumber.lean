/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PentagonalNumber

namespace MetaMathlibExt

example : partitionFunction 0 = 1 := by simp

example : partitionFunction 1 = 1 := by simp

example (n : ℕ) : partitionFunction n = Fintype.card (Nat.Partition n) := rfl

end MetaMathlibExt
