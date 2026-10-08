/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MedianGenocchiDivisibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

/-- The fourth Bernoulli number, used for an independent small-value check. -/
theorem bernoulli_four_for_medianGenocchiOdd : bernoulli 4 = -1 / 30 := by
  have h := sum_bernoulli 5
  simp only [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3] at h
  have c2 : Nat.choose 5 2 = 10 := by decide
  rw [c2] at h
  norm_num at h ⊢
  linarith

/-- The sixth Bernoulli number, used for an independent small-value check. -/
theorem bernoulli_six_for_medianGenocchiOdd : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli 7
  simp only [show (7 : ℕ) = 6 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two,
    bernoulli_four_for_medianGenocchiOdd] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h5 : bernoulli 5 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3, h5] at h
  have c2 : Nat.choose 7 2 = 21 := by decide
  have c4 : Nat.choose 7 4 = 35 := by decide
  rw [c2, c4] at h
  norm_num at h ⊢
  linarith

/-- The eighth Bernoulli number, used for an independent small-value check. -/
theorem bernoulli_eight_for_medianGenocchiOdd : bernoulli 8 = -1 / 30 := by
  have h := sum_bernoulli 9
  simp only [show (9 : ℕ) = 8 + 1 from rfl, Finset.sum_range_succ] at h
  rw [bernoulli_zero, bernoulli_one, bernoulli_two,
    bernoulli_four_for_medianGenocchiOdd, bernoulli_six_for_medianGenocchiOdd] at h
  have h3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h5 : bernoulli 5 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli 7 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [h3, h5, h7] at h
  have c2 : Nat.choose 9 2 = 36 := by decide
  have c4 : Nat.choose 9 4 = 126 := by decide
  have c6 : Nat.choose 9 6 = 84 := by decide
  rw [c2, c4, c6] at h
  norm_num at h ⊢
  linarith

/-- Direct evaluation of the small value used by the `n = 3` consumer test. -/
theorem medianGenocchiOdd_four : MetaMathlibExt.medianGenocchiOdd 4 = 56 := by
  have hg6 : MetaMathlibExt.genocchiNumberViaBernoulli 6 = -3 := by
    rw [MetaMathlibExt.genocchiNumberViaBernoulli,
      bernoulli_six_for_medianGenocchiOdd]
    norm_num
  have hg8 : MetaMathlibExt.genocchiNumberViaBernoulli 8 = 17 := by
    rw [MetaMathlibExt.genocchiNumberViaBernoulli,
      bernoulli_eight_for_medianGenocchiOdd]
    norm_num
  norm_num [MetaMathlibExt.medianGenocchiOdd, hg6, hg8,
    Finset.sum_range_succ]

-- The n = 3 theorem and the direct value computation force quotient seven.
example (h : 1 ≤ (3 : ℕ)) : ∃ z : ℤ,
    MetaMathlibExt.medianGenocchiOdd 4 = (8 : ℚ) * z ∧
      z = 7 ∧ Int.ModEq 6 z 1 := by
  obtain ⟨z, hvalue, hmod⟩ :=
    MetaMathlibExt.medianGenocchiOdd_divisibility 3 h
  have hzq : (z : ℚ) = 7 := by
    rw [medianGenocchiOdd_four] at hvalue
    norm_num at hvalue
    linarith
  have hz : z = 7 := by exact_mod_cast hzq
  refine ⟨z, ?_, hz, ?_⟩
  · norm_num at hvalue ⊢
    exact hvalue
  · have hodd : Odd (3 : ℕ) := by decide
    simpa only [hodd, ↓reduceIte] using hmod

-- The n = 4 theorem gives the even quotient's concrete residue divisibility.
example (h : 1 ≤ (4 : ℕ)) : ∃ z : ℤ,
    MetaMathlibExt.medianGenocchiOdd 5 = (16 : ℚ) * z ∧ 6 ∣ z - 4 := by
  obtain ⟨z, hvalue, hmod⟩ :=
    MetaMathlibExt.medianGenocchiOdd_divisibility 4 h
  refine ⟨z, ?_, (dvd_sub_comm.mp hmod.dvd)⟩
  norm_num at hvalue ⊢
  exact hvalue

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility
