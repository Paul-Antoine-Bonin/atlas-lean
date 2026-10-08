/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Inequality for square-summable complex series
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

open BigOperators

@[expose] public section

namespace MathlibExt.Analysis.SquareSummableComplexInequalityWanted

/-! Source record `OPG-41335`, ported from the Open Problem Garden entry
"Inequality for square summable complex series"
(http://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series).

For `α = (α₁, α₂, …) ∈ ℓ²(ℂ)` the result asserts
`∑ₙ |αₙ|² ≥ (6/π²) ∑ₖ |∑ₗ α_{2ᵏ(2l+1)} / (l+1)|²`,
where every `n ≥ 1` is uniquely written `n = 2ᵏ(2l+1)`.

The sequence is represented by a function on `ℕ`; `α (n + 1)` is its
one-based `n`th term. The two summability conclusions are included explicitly
so totalized `tsum` cannot make the inequality vacuous. -/

def conjecture : Prop :=
  ∀ α : ℕ → ℂ, Summable (fun n => ‖α (n + 1)‖ ^ 2) →
    (∀ k : ℕ, Summable (fun l => α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ))) ∧
    Summable (fun k => ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2) ∧
      ∑' n, ‖α (n + 1)‖ ^ 2 ≥
        6 / Real.pi ^ 2 * ∑' k, ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2

/--
Resolved true: The source page records a Cauchy–Schwarz proof of the displayed inequality.
Source: Open Problem Garden solution comment 73221,
https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series#comment-73221.
Moved from `OpenConjectures/Analysis/SquareSummableComplexInequality`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.SquareSummableComplexInequalityWanted
