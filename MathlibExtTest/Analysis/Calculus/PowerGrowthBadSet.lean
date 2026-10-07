/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.PowerGrowthBadSet

open MeasureTheory Set
open scoped ENNReal

example (h : ℝ → ℝ) {p x₀ : ℝ} (hp : 1 < p)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x)
    (hmono : MonotoneOn h (Ici x₀))
    (hsmooth : ContDiff ℝ 1 h) :
    volume (Real.powerGrowthBadSet h p x₀) < ∞ :=
  Real.volume_powerGrowthBadSet_lt_top h hp hpos hmono hsmooth
