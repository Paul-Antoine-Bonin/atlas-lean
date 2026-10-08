/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.OctagonalPyramidalNumber

namespace MetaMathlibExt

example : octagonalPyramidalNumber 1 = 1 := by decide
example : octagonalPyramidalNumber 4 = 70 := by decide

/-- Regression for the restricted-composition side of the correspondence. -/
example : (octagonalPyramidalCompositions 2).card = 9 := by decide

end MetaMathlibExt
