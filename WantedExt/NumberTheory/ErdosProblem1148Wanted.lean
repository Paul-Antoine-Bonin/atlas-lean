/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1148
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem1148Wanted

/-! Source record `FC-ErdosProblem1148`, ported from FormalConjectures
`ErdosProblems/1148.lean` (`theorem erdos_1148` and its variants) and
checked against erdosproblems.com/1148. The historical question is
preserved as `eventualRepresentation` (established); the weaker
`n + 2√n` bound is the unregistered companion `weakerBound`. Status:
resolved true (Chojecki with GPT-5.4 Pro, conditional on a Duke-type
equidistribution theorem [ELMV12]). -/

/-- `n = x^2 + y^2 - z^2` with `max(x^2, y^2, z^2) ≤ n`. -/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

/-- The weaker `n + 2√n` bound, reported obvious in [Va99]. -/
def weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

/-- Every large integer has such a representation (established). -/
def eventualRepresentation : Prop :=
  ∀ᶠ n in Filter.atTop, Erdos1148Prop n

/-- The weaker bound always holds (established companion). -/
def weakerBound : Prop :=
  ∀ n, weaker_prop n

/--
Resolved true: Resolved affirmatively (Chojecki with GPT-5.4 Pro via Duke-type theorem
[ELMV12]), per erdosproblems.com/1148. Source: P. Chojecki, Bounded Representations by
x^2+y^2-z^2, arXiv:2603.18087 (2026), https://arxiv.org/abs/2603.18087. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1148`.
-/
public theorem_wanted eventualRepresentation_holds : eventualRepresentation

end MathlibExt.NumberTheory.ErdosProblem1148Wanted
