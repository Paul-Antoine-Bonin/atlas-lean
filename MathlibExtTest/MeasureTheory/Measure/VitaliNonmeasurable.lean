/-
  Author: Muse Code powered by Meta Muse Spark
-/
module

import MathlibExt.MeasureTheory.Measure.VitaliNonmeasurable

open MeasureTheory

example : ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) :=
  MeasureTheory.vitali_nonmeasurable
