/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem

example : ¬ Int.IsCoveringSystem ∅ := by
  intro h
  obtain ⟨c, hc, _⟩ := h 0
  exact Finset.notMem_empty c hc

example : Int.IsCoveringSystem {(0, 1)} := by
  intro z
  refine ⟨(0, 1), Finset.mem_singleton_self _, ?_⟩
  rw [Int.modEq_iff_dvd]
  exact one_dvd _

example :
    Int.IsCoveringSystem
      (Int.indexedCoveringClasses (k := 1) (fun _ => 1) (fun _ => 0)) ↔
      ∀ z : ℤ, ∃ i : Fin 1,
        z ≡ (fun _ => (0 : ℤ)) i [ZMOD ((fun _ => 1) i : ℤ)] :=
  Int.indexedCoveringClasses_isCoveringSystem_iff _ _

example :
    Int.IsCoveringSystem
      (Int.indexedCoveringClasses (k := 1) (fun _ => 1) (fun _ => 0)) := by
  rw [Int.indexedCoveringClasses_isCoveringSystem_iff]
  intro z
  refine ⟨0, ?_⟩
  rw [Int.modEq_iff_dvd]
  exact one_dvd _
