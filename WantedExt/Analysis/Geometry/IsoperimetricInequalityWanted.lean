/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- Isoperimetric inequality (statement): for the length `L` of a closed plane curve
and the area `A` of the region it encloses, `4 * π * A ≤ L ^ 2`, with equality
if and only if the curve is a circle.
Source: https://en.wikipedia.org/wiki/Isoperimetric_inequality (isoperimetric-s1). -/
theorem_wanted isoperimetric_inequality
    {g : ℝ → EuclideanSpace ℝ (Fin 2)}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    {L A : ℝ}
    (hg_cont : Continuous g)
    (hg_closed : Function.Periodic g 1)
    (hg_lip : ∃ K, LipschitzWith K g)
    (hg_rect : MeasureTheory.Measure.hausdorffMeasure 1 (Set.range g) ≠ ⊤)
    (hg_simple : Set.InjOn g (Set.Ico (0 : ℝ) 1))
    (hL : L = (MeasureTheory.Measure.hausdorffMeasure 1 (Set.range g)).toReal)
    (hA : A = (MeasureTheory.volume U).toReal)
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_bdd : Bornology.IsBounded U)
    (hU_front : frontier U = Set.range g) :
    4 * Real.pi * A ≤ L ^ 2 ∧
      (4 * Real.pi * A = L ^ 2 ↔
        ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, 0 < r ∧
          Set.range g = Metric.sphere c r)

end

end MetaMathlibExt