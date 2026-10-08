/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.Planarity

example (a b : ℝ × ℝ) : a ∈ SimpleGraph.Segment a b :=
  ⟨0, le_rfl, zero_le_one, by simp, by simp⟩

example (a b : ℝ × ℝ) : b ∈ SimpleGraph.Segment a b :=
  ⟨1, zero_le_one, le_rfl, by rw [one_mul, add_sub_cancel],
    by rw [one_mul, add_sub_cancel]⟩

example : SimpleGraph.IsPlanar (⊥ : SimpleGraph Empty) :=
  Or.inl (fun h => h.elim fun e => Empty.elim e)
