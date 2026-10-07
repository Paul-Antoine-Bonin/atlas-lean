/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NicolNumber

open MetaMathlibExt
open scoped BigOperators

private theorem test_not_nicol_zero : ¬ IsNicolNumber 0 := by
  simp [IsNicolNumber]

private theorem test_nicol_one : IsNicolNumber 1 := by
  exact ⟨by norm_num, one_dvd _⟩

private theorem test_t_nicol_two_one : IsTNicolNumber 2 1 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.totient_one, Nat.divisors_one, Finset.sum_singleton]

example : IsNicolNumber 1 :=
  test_t_nicol_two_one.isNicolNumber

private theorem test_unfold_nicol (n : ℕ) :
    IsNicolNumber n ↔ 0 < n ∧ n ∣ Nat.totient n + ∑ d ∈ n.divisors, d :=
  Iff.rfl

private theorem test_unfold_t_nicol (t n : ℕ) :
    IsTNicolNumber t n ↔
      0 < n ∧ Nat.totient n + ∑ d ∈ n.divisors, d = t * n :=
  Iff.rfl
