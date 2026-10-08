/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Sets of finite Lebesgue measure

This file records an elementary unbounded-complement property of subsets of the real line
with finite Lebesgue measure.
-/

@[expose] public section

namespace MeasureTheory

open Set
open scoped ENNReal

/-- A set of finite Lebesgue measure cannot contain a right half-line. -/
theorem exists_gt_not_mem_of_volume_lt_top
    (E : Set ℝ) (hE : volume E < ∞) (X : ℝ) :
    ∃ x : ℝ, X < x ∧ x ∉ E := by
  by_contra! h
  have hmono : volume (Ioi X) ≤ volume E := measure_mono fun x hx ↦ h x hx
  have htop : (∞ : ℝ≥0∞) ≤ volume E := by
    simpa only [Real.volume_Ioi] using hmono
  exact (not_lt_of_ge htop) hE

end MeasureTheory
