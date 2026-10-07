/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.KAbelianSquareFreeWord

namespace MetaMathlibExt

example : wordFactorCount ([0, 0, 0] : List ℕ) [0, 0] = 2 := by decide
example : wordFactorCount ([0, 1, 0] : List ℕ) [0] = 2 := by decide
example : wordFactorCount ([0, 1] : List ℕ) [] = 0 := by decide

end MetaMathlibExt
