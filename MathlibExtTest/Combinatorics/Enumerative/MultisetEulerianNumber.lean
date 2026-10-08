/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MultisetEulerianNumber

namespace MetaMathlibExt

private def twoTwoMultiplicity : Fin 2 → ℕ := fun _ => 2

example : multisetEulerianNumber twoTwoMultiplicity 1 = 1 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 2 = 4 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 3 = 1 := by decide
example : multisetEulerianNumber twoTwoMultiplicity 4 = 0 := by decide

#print axioms multisetDescentNumber
#print axioms IsMultisetPermutation
#print axioms multisetEulerianNumber

end MetaMathlibExt
