/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 728
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter
open scoped Nat Topology

namespace MathlibExt.NumberTheory.ErdosProblem728Wanted

/-! Source record `FC-ErdosProblem728`, ported from FormalConjectures
`ErdosProblems/728.lean` (`theorem erdos_728`) and checked against
erdosproblems.com/728. The upstream `answer(True)` is dropped. Status:
resolved true externally by Barreto and ChatGPT-5.2. This module states the
result but does not prove it; a pinned external Lean proof is in the registry. -/

/-- Factorial divisibility with `O(log n)` window. -/
def conjecture : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
    ∃ a b n : ℕ,
      0 < n ∧
      ε * n < a ∧
      ε * n < b ∧
      a ! * b ! ∣ n ! * (a + b - n)! ∧
      a + b > n + C * Real.log n ∧
      a + b < n + C' * Real.log n

/--
Resolved true: Resolved externally by Barreto and ChatGPT-5.2. This repository records the
statement, not an internal proof; a pinned external Lean proof is cited below. Source: N.
Sothanaphan, Resolution of Erdős Problem #728: a writeup of Aristotle's Lean proof,
arXiv:2601.07421 (2026), https://arxiv.org/abs/2601.07421. Moved from
`OpenConjectures/NumberTheory/ErdosProblem728`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem728Wanted
