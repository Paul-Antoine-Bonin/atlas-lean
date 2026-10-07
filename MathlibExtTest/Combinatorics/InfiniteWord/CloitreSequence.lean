/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence

namespace MetaMathlibExt

example : cloitreApprox 2 = [1, 1, 2, 1, 1, 1, 1] := by decide

example : (List.range 15).map cloitreSequence =
    [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2] := by
  decide

end MetaMathlibExt
