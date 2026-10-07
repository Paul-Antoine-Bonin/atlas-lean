/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.DiscreteSpectrum

/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/

open scoped BigOperators

namespace NonnegativeDiscreteSpectrumTest

/-- Doubling-index eigenvalues `0, 0, 1, 1, 2, 2, …`: the value `0` has
multiplicity two (indices `0` and `1`). -/
def dupEigen : ℕ → ℝ := fun j => ((j / 2 : ℕ) : ℝ)

/-- The doubling-index spectrum as a `NonnegativeDiscreteSpectrum`. -/
noncomputable def dupSpectrum : NonnegativeDiscreteSpectrum where
  eigenvalue := dupEigen
  nonnegative_eigenvalue := fun j => Nat.cast_nonneg _
  monotone_eigenvalue := by
    intro a b hab
    change ((a / 2 : ℕ) : ℝ) ≤ ((b / 2 : ℕ) : ℝ)
    exact Nat.cast_le.mpr (by omega)
  tendsto_eigenvalue_atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge b
    exact ⟨2 * n, fun a ha => le_trans hn (Nat.cast_le.mpr (by omega))⟩

-- Every public projection and theorem is exercised below.

example : dupSpectrum.eigenvalue = dupEigen := rfl

example (j : ℕ) : 0 ≤ dupSpectrum.eigenvalue j :=
  dupSpectrum.nonnegative_eigenvalue j

example : Monotone dupSpectrum.eigenvalue := dupSpectrum.monotone_eigenvalue

example : Filter.Tendsto dupSpectrum.eigenvalue Filter.atTop Filter.atTop :=
  dupSpectrum.tendsto_eigenvalue_atTop

example : dupSpectrum.sublevelSet 1 = {j | dupSpectrum j < 1} := rfl

example : (dupSpectrum.sublevelSet 1).Finite := dupSpectrum.sublevelSet_finite 1

example (j : ℕ) : j ∈ dupSpectrum.sublevelFinset 1 ↔ dupSpectrum j < 1 :=
  dupSpectrum.mem_sublevelFinset 1 j

-- A repeated eigenvalue is counted once per index (multiplicity).
example : dupEigen 0 = dupEigen 1 := rfl

example : (0 : ℕ) ∈ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change dupEigen 0 < 1
  norm_num [dupEigen]

example : (1 : ℕ) ∈ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change dupEigen 1 < 1
  norm_num [dupEigen]

-- An eigenvalue equal to the cutoff is excluded from the strict sublevel.
example : dupEigen 2 = 1 := by norm_num [dupEigen]

example : (2 : ℕ) ∉ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change ¬ dupEigen 2 < 1
  norm_num [dupEigen]

/-- Membership below the cutoff `1` is exactly `j = 0 ∨ j = 1`. -/
theorem dup_mem_iff (j : ℕ) : dupSpectrum j < 1 ↔ j = 0 ∨ j = 1 := by
  change dupEigen j < 1 ↔ _
  unfold dupEigen
  constructor
  · intro h
    have h1 : j / 2 < 1 := by exact_mod_cast h
    have h2 : j / 2 = 0 := Nat.lt_one_iff.mp h1
    omega
  · rintro (rfl | rfl) <;> norm_num

/-- The strict sublevel finset below `1` is exactly `{0, 1}`. -/
theorem dup_sublevelFinset_one : dupSpectrum.sublevelFinset 1 = {0, 1} := by
  ext j
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset, dup_mem_iff,
    Finset.mem_insert, Finset.mem_singleton]

/-- Counting below `1` sees both copies of the repeated eigenvalue. -/
theorem dup_counting_one : dupSpectrum.countingFunction 1 = 2 := by
  change (dupSpectrum.sublevelFinset 1).card = 2
  rw [dup_sublevelFinset_one]
  decide

-- The `σ = 0` Riesz mean recovers the counting function.
example : dupSpectrum.rieszMean 0 1 = dupSpectrum.countingFunction 1 :=
  dupSpectrum.rieszMean_zero 1

example : dupSpectrum.rieszMean 0 1 = 2 := by
  rw [dupSpectrum.rieszMean_zero, dup_counting_one]
  norm_num

-- A Riesz mean with `σ = 1` over the two surviving terms.
example : dupSpectrum.rieszMean 1 1 = 2 := by
  change ∑ j ∈ dupSpectrum.sublevelFinset 1, Real.rpow (1 - dupSpectrum j) 1 = 2
  rw [dup_sublevelFinset_one]
  have e0 : dupSpectrum (0 : ℕ) = 0 := by
    change dupEigen 0 = 0
    norm_num [dupEigen]
  have e1 : dupSpectrum (1 : ℕ) = 0 := by
    change dupEigen 1 = 0
    norm_num [dupEigen]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    e0, e1]
  have hr : ∀ x : ℝ, x.rpow (1 : ℝ) = x := fun x => Real.rpow_one x
  rw [hr]
  norm_num

/-- A second copy of the doubling-index spectrum with independently supplied
proof fields. -/
noncomputable def dupSpectrumAlt : NonnegativeDiscreteSpectrum where
  eigenvalue := dupEigen
  nonnegative_eigenvalue := fun j => Nat.cast_nonneg _
  monotone_eigenvalue := by
    intro a b hab
    change ((a / 2 : ℕ) : ℝ) ≤ ((b / 2 : ℕ) : ℝ)
    exact Nat.cast_le.mpr (by omega)
  tendsto_eigenvalue_atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge b
    exact ⟨2 * n + 1, fun a ha => le_trans hn (Nat.cast_le.mpr (by omega))⟩

-- Pointwise extensionality identifies spectra with the same eigenvalue function.
example : dupSpectrum = dupSpectrumAlt := by
  ext j
  rfl

end NonnegativeDiscreteSpectrumTest
