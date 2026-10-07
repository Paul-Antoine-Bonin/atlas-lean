/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FubiniNumber

namespace MetaMathlibExt

example : (List.range 5).map fubiniNumber = [1, 1, 3, 13, 75] := by decide

example : fubiniNumber 0 = 1 := by simp

example : fubiniNumber 1 = 1 := by simp

example : fubiniNumber 2 = 3 := fubiniNumber_two

end MetaMathlibExt
