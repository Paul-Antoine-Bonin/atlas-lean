/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.FirstDifference

namespace MetaMathlibExt

example (w : ℕ → ZMod 2) : firstDifference w 0 = w 1 - w 0 := by
  rfl

example : firstDifferenceList [] = [] := by
  rfl

example : firstDifferenceList ([0, 1, 1, 0, 1, 0] : List (ZMod 2)) = [1, 0, 1, 1, 1] := by
  decide

#print axioms firstDifference
#print axioms firstDifferenceList
#print axioms length_firstDifferenceList

end MetaMathlibExt
