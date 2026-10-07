/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.PrimitiveWord

namespace MetaMathlibExt

example : ¬ IsPrimitiveWord ([] : List ℕ) := by
  simp [IsPrimitiveWord]

example : ¬ IsPrimitiveWord [0, 0] := by
  intro h
  have hn : 2 = 1 := h.2 [0] 2 (by rfl)
  simp at hn

example {α : Type*} (a : α) : IsPrimitiveWord [a] := by
  constructor
  · simp
  · intro v n h
    have hlength : n * v.length = 1 := by
      simpa using congrArg List.length h
    exact Nat.dvd_one.mp ⟨v.length, hlength.symm⟩

#print axioms IsPrimitiveWord

end MetaMathlibExt
