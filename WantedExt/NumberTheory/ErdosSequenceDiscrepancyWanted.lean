/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 992: discrepancy of fractional parts of `α * xₙ`

Erdős Problem 992 asks: for integers `x₁ < x₂ < ⋯`, is it true that for
almost all `α ∈ [0, 1]` the discrepancy
`D(N) = max over intervals I of |count - |I| * N|` satisfies
`D(N) ≪ N ^ (1/2) * (log N) ^ o(1)`?

Gaps vs the source record:
- Only the first (weaker) bound is formalized; the stronger
  `(log log N)`-variant mentioned in the record is omitted.
- The record takes the maximum over all intervals; here the discrepancy is
  the supremum over closed intervals with rational endpoints in `[0, 1]`
  (so that counting is well-defined with decidable membership), which
  approximates the full-interval supremum.
- Indexing is 0-based (`x : ℕ → ℤ` with `StrictMono x`) rather than 1-based.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted

/-! Source record `EP-992`. -/
open MeasureTheory Filter

open Classical in
/-- Count of `n < N` with the fractional part of `α * x n` in the rational
closed interval `[p, q]`. -/
noncomputable def CountQ (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (p q : ℚ) : ℕ :=
  ((Finset.range N).filter fun n =>
    Int.fract (α * (x n : ℝ)) ∈ Set.Icc (p : ℝ) (q : ℝ)).card

/-- Discrepancy: supremum over rational-endpoint closed intervals in `[0, 1]`
of `|count - length * N|`. -/
noncomputable def discrep (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup { d : ℝ | ∃ p q : ℚ, 0 ≤ (p : ℝ) ∧ (q : ℝ) ≤ 1 ∧ (p : ℝ) ≤ (q : ℝ) ∧
    d = |(CountQ x α N p q : ℝ) - ((q : ℝ) - (p : ℝ)) * (N : ℝ)| }

/-- [EP-992] For every strictly increasing integer sequence, for almost every
`α ∈ [0, 1]` (Lebesgue measure), the discrepancy is `O(√N * (log N)^ε)`
eventually in `N`, for every `ε > 0`. -/
def conjecture : Prop :=
  ∀ x : ℕ → ℤ, StrictMono x →
    ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ᶠ N : ℕ in atTop,
          discrep x α N ≤ C * Real.sqrt (N : ℝ) * Real.rpow (Real.log (N : ℝ)) ε

/--
Resolved false: Berkes and Philipp (J. London Math. Soc. 50 (1994) 454-464) construct an
increasing integer sequence with limsup |Σ_{k≤N} cos(2πn_k α)|/√(N log N) = ∞ for a.e. α; by
Koksma's inequality D(N) is then not O(√N (log N)^ε) for ε<1/2, so the Lean statement is false.
Source: C. Aistleitner, I. Berkes, R. Tichy, Lacunary sequences in analysis, probability and
number theory, arXiv preprint (2023), arXiv:2301.05561 (reporting I. Berkes, W. Philipp, J.
London Math. Soc. (2) 50 (1994), 454-464), https://arxiv.org/abs/2301.05561. Moved from
`OpenConjectures/NumberTheory/ErdosSequenceDiscrepancy`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosSequenceDiscrepancyWanted
