/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR

namespace MetaMathlibExt.ULDMotzkin

private def ones : Fin 1 → ℕ := fun _ => 1

example : uldMotzkinNumber 1 ones 1 ones (by decide) 0 = 1 := by decide
example : uldMotzkinNumber 1 ones 1 ones (by decide) 2 = 2 := by decide

end MetaMathlibExt.ULDMotzkin
