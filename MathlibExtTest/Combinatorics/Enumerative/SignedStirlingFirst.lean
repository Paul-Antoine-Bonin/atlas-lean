/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

namespace MetaMathlibExt

example : signedStirlingFirst 3 1 = 2 := by decide

example : signedStirlingFirst 3 2 = -3 := by decide

example : signedStirlingFirst 5 5 = 1 := signedStirlingFirst_self 5

example : signedStirlingFirst 2 3 = 0 := signedStirlingFirst_eq_zero_of_lt (by decide)

end MetaMathlibExt
