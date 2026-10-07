/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Analysis.Complex.Wiman

@[expose] public section

namespace MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted

open Complex (wimanTaylorCoefficient)

/-!
# Research Problems in Function Theory — Problem 6.46

Source clause list (every item appears in the formal text below):
1. `f` is in the class `S`: analytic in the unit disc, normalized by
  `f 0 = 0` and `f'(0) = 1`, and univalent (injective) on the unit disc.
2. `f` is star-like: `Re (z * f'(z) / f z) > 0` for `z ≠ 0` in the unit disc.
3. `a n` denotes the Taylor coefficient of `f` at `0`
  (`iteratedDeriv n f 0 / n!`).
4. Quantifier domain: all such `f`, all `n : ℕ` with `1 ≤ n`.
5. Questioned bound: `‖ |a (n+1)| - |a n| ‖ ≤ 1`, stated as the
  source's question (a `Prop` with no proof in this repository).
-/

/-- Class `S` from Hayman and Lingham, Research Problems in Function Theory (2018),
Problem 6.46 (https://arxiv.org/abs/1809.07200): normalized univalent
analytic functions on the unit disc. -/
def IsInClassS (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    f 0 = 0 ∧ HasDerivAt f 1 0 ∧ Set.InjOn f (Metric.ball (0 : ℂ) 1)

/-- Star-like functions from Hayman, Research Problems in Function Theory
(2018), Problem 6.46 (https://arxiv.org/abs/1809.07200): positive real part
of `z * f'(z) / f z` off `0` in the unit disc. -/
def IsStarlike (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → 0 < (z * deriv f z / f z).re

/-- Question of Hayman and Lingham, Research Problems in Function Theory (2018),
Problem 6.46 (https://arxiv.org/abs/1809.07200): if `f` is in `S` and star-like, with Taylor
coefficients `a n` at `0`, is `‖ |a (n+1)| - |a n| ‖ ≤ 1` for all `n ≥ 1`? -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, IsInClassS f → IsStarlike f →
    ∀ n : ℕ, 1 ≤ n → |‖wimanTaylorCoefficient f (n + 1)‖ - ‖wimanTaylorCoefficient f n‖| ≤ 1
/--
Resolved true: Y. Leung (Bull. London Math. Soc. 10 (1978), 193-196) proved ||a_{n+1}|-|a_n|| <=
1 for every n >= 1 and every starlike f in S, answering Problem 6.46 affirmatively; D. H.
Hamilton proved it independently. Source: Moduli difference of initial inverse logarithmic
coefficients for starlike and convex functions (2026), arXiv:2603.17600,
https://arxiv.org/abs/2603.17600. Moved from
`OpenConjectures/Analysis/StarlikeCoefficientSuccessiveDifference`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted
