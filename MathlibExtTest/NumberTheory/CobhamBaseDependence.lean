/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CobhamBaseDependence

-- The even numbers are ultimately periodic with period 2.
example : MetaMathlibExt.IsUltimatelyPeriodic
    (fun n => n ∈ ({n : ℕ | Even n} : Set ℕ)) := by
  rw [← MetaMathlibExt.isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic]
  refine ⟨0, 2, by norm_num, fun n _ => ?_⟩
  change Even n ↔ Even (n + 2)
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r + 1, by omega⟩
  · rintro ⟨r, h⟩
    have hr : 1 ≤ r := by omega
    exact ⟨r - 1, by omega⟩

-- Cobham dependence for bases 2 and 3 from local hypotheses.
example (S : Set ℕ)
    (hindependent : MetaMathlibExt.BasesMultiplicativelyIndependent 2 3)
    (hrecognizable : MetaMathlibExt.IsBaseRecognizable 2 S)
    (haperiodic : ¬ MetaMathlibExt.IsUltimatelyPeriodic (fun n => n ∈ S)) :
    ¬ MetaMathlibExt.IsBaseRecognizable 3 S :=
  MetaMathlibExt.cobham_base_dependence_isUltimatelyPeriodic
    (by norm_num) hindependent hrecognizable haperiodic
