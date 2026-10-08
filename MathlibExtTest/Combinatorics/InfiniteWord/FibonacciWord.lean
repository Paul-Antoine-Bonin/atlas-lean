/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord

namespace MetaMathlibExt

example : fibWord 4 =
    [false, true, false, false, true, false, true, false] := rfl

example : (List.range 8).map fibInf =
    [false, true, false, false, true, false, true, false] := by
  decide

end MetaMathlibExt
