/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SmarandachePermutationSequence

namespace MetaMathlibExt

example : smarandacheBlock 4 = [1, 3, 5, 7, 8, 6, 4, 2] := by rfl
example : List.map smarandachePermutation (List.range 6) = [1, 2, 1, 3, 4, 2] := by rfl

end MetaMathlibExt
