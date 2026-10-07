/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Measure.Lebesgue.Finite

open MeasureTheory Set
open scoped ENNReal

example (E : Set ℝ) (hE : volume E < ∞) (X : ℝ) :
    ∃ x : ℝ, X < x ∧ x ∉ E :=
  MeasureTheory.exists_gt_not_mem_of_volume_lt_top E hE X
