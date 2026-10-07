/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CoveringSystem.ExactCover

example : Int.indexedCoverMultiplicity (fun _ : Fin 2 => 2)
    (fun i => (i : ℕ)) 0 = 1 := by decide

example {k M : ℕ} {moduli : Fin k → ℕ} {residues : Fin k → ℤ} {target : Set ℤ}
    (h : Int.IsExactCoverOf moduli residues M target) : 2 ≤ k :=
  h.1
