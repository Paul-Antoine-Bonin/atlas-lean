/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.OctanacciNumber

namespace MetaMathlibExt

example : octanacciNumber 0 = 1 := by decide
example : octanacciNumber 8 = 128 := by decide
example : octanacciNumber 9 = 255 := by decide

end MetaMathlibExt
