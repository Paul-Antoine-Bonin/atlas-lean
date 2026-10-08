/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Measure.VitaliNonmeasurable

open MeasureTheory

example : ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) :=
  MeasureTheory.vitali_nonmeasurable
