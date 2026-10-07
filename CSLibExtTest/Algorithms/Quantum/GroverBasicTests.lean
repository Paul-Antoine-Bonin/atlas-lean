/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Symmetry
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Basic tests for Grover search

These examples exercise the standard four-state search with one marked state.
Starting from the uniform amplitude `1 / 2`, one Grover iteration places
amplitude `1` on the marked state and `0` on every unmarked state.
-/

namespace Cslib.Grover.BasicTests

open scoped BigOperators

def oneMarked : Finset (Fin 4) := {0}

noncomputable def uniformFour : Amplitude (Fin 4) := fun _ => 1 / 2

example : phaseOracle oneMarked uniformFour 0 = -1 / 2 := by
  norm_num [phaseOracle, oneMarked, uniformFour]

example : meanAmplitude (phaseOracle oneMarked uniformFour) = 1 / 4 := by
  norm_num [meanAmplitude, phaseOracle, oneMarked, uniformFour, Fin.sum_univ_succ]

example : groverStep oneMarked uniformFour 0 = 1 := by
  norm_num [groverStep, diffusion, meanAmplitude, phaseOracle, oneMarked,
    uniformFour, Fin.sum_univ_succ]

example (i : Fin 4) (hi : i ≠ 0) : groverStep oneMarked uniformFour i = 0 := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    norm_num [groverStep, diffusion, meanAmplitude, phaseOracle, oneMarked,
      uniformFour, Fin.sum_univ_succ]

example : markedProbability oneMarked (groverStep oneMarked uniformFour) = 1 := by
  norm_num [markedProbability, groverStep, diffusion, meanAmplitude, phaseOracle,
    oneMarked, uniformFour, Fin.sum_univ_succ]

end Cslib.Grover.BasicTests
