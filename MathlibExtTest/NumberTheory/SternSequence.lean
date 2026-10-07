/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SternSequence

namespace MetaMathlibExt

example : sternSequence 0 = 0 := stern_zero

example : sternSequence 1 = 1 := stern_one

example : sternSequence 2 = 1 := by
  simpa [stern_one] using stern_even 1 (by decide)

example : sternSequence 3 = 2 := by
  have htwo : sternSequence 2 = 1 := by
    simpa [stern_one] using stern_even 1 (by decide)
  simpa [stern_one, htwo] using stern_odd 1 (by decide)

example : sternSequence (2 * 1) = sternSequence 1 :=
  stern_even 1 (by decide)

example : sternSequence (2 * 1 + 1) = sternSequence 1 + sternSequence (1 + 1) :=
  stern_odd 1 (by decide)

end MetaMathlibExt
