/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GiugaNumber

namespace MetaMathlibExt

@[expose] public section

example (n : ℕ) : IsGiugaNumber n ↔
    2 ≤ n ∧ ¬ Nat.Prime n ∧ ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1) := Iff.rfl

example : ¬ IsGiugaNumber 0 := by
  simp [IsGiugaNumber]

example : ¬ IsGiugaNumber 1 := by
  simp [IsGiugaNumber]

#print axioms IsGiugaNumber

end

end MetaMathlibExt
