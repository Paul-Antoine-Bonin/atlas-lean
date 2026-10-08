/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KeithNumber

namespace MetaMathlibExt

example : keithSequence [1, 9, 7] 0 = 1 := rfl
example : keithSequence [1, 9, 7] 1 = 9 := rfl
example : keithSequence [1, 9, 7] 2 = 7 := rfl
example : keithSequence [1, 9, 7] 3 = 17 := rfl
example : keithSequence [1, 9, 7] 7 = 197 := rfl

example : IsKeithNumberWithDigits 197 [1, 9, 7] := by
  refine ⟨by decide, by decide, by decide, by decide, 7, by decide, ?_⟩
  rfl

example : IsKeithNumber 197 := by
  refine ⟨[1, 9, 7], by decide, by decide, by decide, by decide, 7, by decide, ?_⟩
  rfl

example : ¬ IsKeithNumberWithDigits 7 [7] := by
  simp [IsKeithNumberWithDigits]

#print axioms keithSequence
#print axioms IsKeithNumberWithDigits
#print axioms IsKeithNumber

end MetaMathlibExt
