/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rademacher LIL constant
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.NumberTheory.RandomMultiplicativeFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.LiminfLimsup

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators
open MetaMathlibExt.RandomMultiplicativeFunction

namespace MathlibExt.NumberTheory.RademacherLILConstantWanted

/-! Source record `EP-520__2155`. -/

/-- Partial sum of the Rademacher function over `1..N` at `ω`. -/
noncomputable def partialSum {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (ω : Ω)
    (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ((rademacherFunction X ω m : ℤ) : ℝ)

/-- Open question of [EP-520]: does there exist a constant `c > 0` such that,
    almost surely, the limsup of the normalized partial sums equals `c`? -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Nat.Primes → Ω → ℤˣ),
    IsRademacherFamily μ X →
    ∀ᵐ ω ∂μ, Filter.limsup
      (fun N : ℕ => partialSum X ω N /
        Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) Filter.atTop = c

/--
Resolved false: Durkan and Pearce-Crump (arXiv:2607.29429, 2026) and independently Verreault
(arXiv:2608.21354, 2026) prove that a Rademacher random multiplicative function a.s. has
|Σ_{n≤x} f(n)| ≪ √x (log log x)^{1/4+ε}, so the normalized limsup is a.s. 0 and no constant c>0
works. Source: B. Durkan, A. Pearce-Crump, A sharp almost sure upper bound for partial sums of
random multiplicative functions, arXiv preprint (2026), arXiv:2607.29429,
https://arxiv.org/abs/2607.29429; W. Verreault, Almost sure upper bound for sums of random
multiplicative functions and critical chaos, arXiv preprint (2026), arXiv:2608.21354,
https://arxiv.org/abs/2608.21354. Moved from
`OpenConjectures/NumberTheory/RademacherLILConstant`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.RademacherLILConstantWanted
