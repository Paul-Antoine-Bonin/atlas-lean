/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.LaplaceTransform.BasicProperties
public import MathlibExt.Analysis.LaplaceTransform.NewmanTauberian

/-!
# Tests for Newman's Tauberian theorem.
-/

open MeasureTheory Topology

example (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG_analytic : AnalyticOnNhd ℂ G {s | 0 ≤ s.re})
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s)) :
    Filter.Tendsto (fun T : ℝ => ∫ t : ℝ in (0 : ℝ)..T, f t)
      Filter.atTop (𝓝 (G 0)) :=
  newman_tauberian f B hfmeas hB hbound G hG_analytic hG

example : Filter.Tendsto (fun T : ℝ => ∫ _ : ℝ in (0 : ℝ)..T, (0 : ℂ))
    Filter.atTop (𝓝 ((fun _ : ℂ => (0 : ℂ)) 0)) :=
  newman_tauberian _ 0 continuous_const.aestronglyMeasurable le_rfl
    (fun _ _ => by simp) _ analyticOnNhd_const (fun s _ => hasLaplace_zero s)
