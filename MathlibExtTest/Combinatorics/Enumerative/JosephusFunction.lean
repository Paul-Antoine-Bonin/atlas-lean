/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

namespace MetaMathlibExt

example : josephus 2 5 = 3 := by decide
example : josephus 3 5 = 4 := by decide
example : 1 ≤ josephus 8 3 ∧ josephus 8 3 ≤ 3 := by decide

end MetaMathlibExt
