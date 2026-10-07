/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.RiemannRearrangement

namespace MathlibExtTest.Analysis.Series.RiemannRearrangement

open MathlibExt.Analysis.Series.RiemannRearrangementWanted

example : OrderedHasSum (fun _ => 0) 0 := by
  rw [orderedHasSum_iff]
  simp

example (f : ℕ → ℝ) (s : ℝ) (h : OrderedHasSum f s) :
    Filter.Tendsto f Filter.atTop (nhds 0) :=
  orderedHasSum_tendsto_zero f s h

end MathlibExtTest.Analysis.Series.RiemannRearrangement
