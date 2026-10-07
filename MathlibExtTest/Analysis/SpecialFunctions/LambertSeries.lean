/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import MathlibExt.Analysis.SpecialFunctions.LambertSeries

namespace MetaMathlibExt

private noncomputable def zeroInUnitDisk : {q : ℂ // ‖q‖ < 1} :=
  ⟨0, by norm_num⟩

example (k : ℕ) : lambertSeriesSummand zeroInUnitDisk k = 0 := by
  simp [lambertSeriesSummand, zeroInUnitDisk]

example : lambertSeries zeroInUnitDisk = 0 := by
  simp [lambertSeries, lambertSeriesSummand, zeroInUnitDisk]

example (k : ℕ) : lambertGSummand zeroInUnitDisk k = 0 := by
  simp [lambertGSummand, zeroInUnitDisk]

end MetaMathlibExt
