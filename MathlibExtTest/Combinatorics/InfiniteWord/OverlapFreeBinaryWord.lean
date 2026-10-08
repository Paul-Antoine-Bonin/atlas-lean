/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.OverlapFreeBinaryWord

namespace MetaMathlibExt

example : IsWordOverlap ([false, true, false, true, false] : List Bool) := by
  refine ⟨[false], [true], by simp, ?_⟩
  rfl

example : IsWordOverlap
    ([false, true, true, false, true, true, false, true] : List Bool) := by
  refine ⟨[false, true], [true], by simp, ?_⟩
  rfl

example : IsOverlapFreeBinaryWord [] := by
  simp [IsOverlapFreeBinaryWord, IsWordOverlap]

end MetaMathlibExt
