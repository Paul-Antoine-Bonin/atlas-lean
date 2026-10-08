/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MedianGenocchiNumber

namespace MetaMathlibExt

example : medianGenocchiOdd 0 = 1 := by simp
example : medianGenocchiOdd 1 = -1 := by simp

end MetaMathlibExt
