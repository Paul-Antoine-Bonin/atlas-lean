/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Analysis
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Tests for exact Grover analysis

The one-marked-state example checks both the concrete finite-state computation
and the exact sine-squared theorem. A two-marked-state example instantiates the
same theorem for a genuinely multiple-target search.
-/

namespace Cslib.Grover.AnalysisTests

def oneMarked : Finset (Fin 4) := {0}

def twoMarked : Finset (Fin 4) := {0, 1}

theorem oneMarked_nonempty : oneMarked.Nonempty := by
  simp [oneMarked]

theorem oneMarked_compl_nonempty : oneMarkedᶜ.Nonempty := by
  refine ⟨1, ?_⟩
  simp [oneMarked]

theorem twoMarked_nonempty : twoMarked.Nonempty := by
  simp [twoMarked]

theorem twoMarked_compl_nonempty : twoMarkedᶜ.Nonempty := by
  refine ⟨2, ?_⟩
  simp [twoMarked]

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

example (k : ℕ) :
    markedProbability oneMarked
        (groverIterate oneMarked k (uniformAmplitude (Fin 4))) =
      (Real.sin (groverPhase oneMarked k)) ^ 2 :=
  markedProbability_groverIterate_uniform oneMarked oneMarked_nonempty
    oneMarked_compl_nonempty k

example :
    markedProbability oneMarked
        (groverIterate oneMarked 1 (uniformAmplitude (Fin 4))) = 1 := by
  norm_num [groverIterate, groverStep, diffusion, meanAmplitude, phaseOracle,
    markedProbability, uniformAmplitude, oneMarked, Fin.sum_univ_succ, sqrt_four]

example : (Real.sin (groverPhase oneMarked 1)) ^ 2 = 1 := by
  rw [← markedProbability_groverIterate_uniform oneMarked oneMarked_nonempty
    oneMarked_compl_nonempty]
  norm_num [groverIterate, groverStep, diffusion, meanAmplitude, phaseOracle,
    markedProbability, uniformAmplitude, oneMarked, Fin.sum_univ_succ, sqrt_four]

example (k : ℕ) :
    markedProbability twoMarked
        (groverIterate twoMarked k (uniformAmplitude (Fin 4))) =
      (Real.sin (groverPhase twoMarked k)) ^ 2 :=
  markedProbability_groverIterate_uniform twoMarked twoMarked_nonempty
    twoMarked_compl_nonempty k

end Cslib.Grover.AnalysisTests
