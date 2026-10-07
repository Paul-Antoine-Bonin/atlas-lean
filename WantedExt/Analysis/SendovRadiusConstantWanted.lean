/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.SendovRadiusConstantWanted

/-!
# Sendov radius constant
-/

/-- A positive radius is admissible if, for every complex polynomial of degree at least two
whose zeros all lie in the closed unit disk, every zero has a critical point within that closed
radius. -/
def IsAdmissibleRadius (R : ℝ) : Prop :=
  0 < R ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ f : Polynomial ℂ, f.natDegree = n →
        (∀ z : ℂ, f.eval z = 0 → ‖z‖ ≤ 1) →
          ∀ lambda0 : ℂ, f.eval lambda0 = 0 →
            ∃ c : ℂ, f.derivative.eval c = 0 ∧ ‖c - lambda0‖ ≤ R

/-- Increasing an admissible radius preserves admissibility. -/
theorem IsAdmissibleRadius.mono {R S : ℝ} (hR : IsAdmissibleRadius R) (hRS : R ≤ S) :
    IsAdmissibleRadius S := by
  refine ⟨lt_of_lt_of_le hR.1 hRS, ?_⟩
  intro n hn f hdeg hroots lambda0 hlambda0
  obtain ⟨c, hc, hdist⟩ := hR.2 n hn f hdeg hroots lambda0 hlambda0
  exact ⟨c, hc, hdist.trans hRS⟩

/-- The infimum of the admissible positive radii in Sendov's problem. -/
noncomputable def sendovRadius : ℝ :=
  sInf {R : ℝ | IsAdmissibleRadius R}

/-- The set of admissible radii is bounded below by zero. -/
theorem bddBelow_admissibleRadii : BddBelow {R : ℝ | IsAdmissibleRadius R} :=
  ⟨0, fun _ hR ↦ le_of_lt hR.1⟩

/-- Every admissible radius is an upper bound for the Sendov radius. -/
theorem sendovRadius_le_of_isAdmissibleRadius {R : ℝ} (hR : IsAdmissibleRadius R) :
    sendovRadius ≤ R := by
  rw [sendovRadius]
  exact csInf_le bddBelow_admissibleRadii hR

/-- Sendov's conjecture, expressed as the radius bound `sendovRadius ≤ 1`. -/
def sendovConjecture : Prop :=
  sendovRadius ≤ 1

/-- The standard example `z ^ n - 1` gives the lower bound one. -/
def lowerBoundOne : Prop :=
  1 ≤ sendovRadius

/-- The geometric bound from Gauss–Lucas gives the upper bound two. -/
def upperBoundTwo : Prop :=
  sendovRadius ≤ 2

/--
Resolved true: Lech Mazur's 2026 computer-assisted proof establishes Sendov's conjecture; the
teorth/sendov Lean development proves the exact closed-unit-disk statement, so the Sendov radius
satisfies C69 ≤ 1. Source: Lech Mazur, A Computer-Assisted Proof of Sendov's Conjecture,
ProofAtlas, August 5, 2026,
https://www.proofatlas.ai/papers/sendov-conjecture/SENDOV_CONJECTURE_PROOF_AUGUST_5_2026.pdf;
teorth/sendov, Sendov's conjecture in Lean, commit 1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d,
https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean.
Moved from `OpenConjectures/Analysis/SendovRadiusConstant`.
-/
public theorem_wanted sendovConjecture_holds : sendovConjecture

end MathlibExt.Analysis.SendovRadiusConstantWanted
