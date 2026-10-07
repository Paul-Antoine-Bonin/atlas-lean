/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PracticalNumber

namespace MetaMathlibExt

example : ¬ IsPracticalNumber 0 := by
  simp [IsPracticalNumber]

example : IsPracticalNumber 1 := by
  refine ⟨by omega, ?_⟩
  intro m hm hmn
  have hm_one : m = 1 := by omega
  subst m
  refine ⟨{1}, ?_, ?_⟩
  · simp
  · simp

example (n : ℕ) (h : IsPracticalNumber n) : 0 < n := h.1

example (n m : ℕ) (h : IsPracticalNumber n) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ x ∈ s, x = m := h.2 m hm hmn

#print axioms IsPracticalNumber

end MetaMathlibExt
