/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedRobbinsNumber

namespace MetaMathlibExt

example : robbinsNumber 0 = 1 := by decide
example : robbinsNumber 3 = 7 := by decide
example : signedRobbinsNumber 0 = 1 := by decide
example : signedRobbinsNumber 2 = -7 := by decide

end MetaMathlibExt
