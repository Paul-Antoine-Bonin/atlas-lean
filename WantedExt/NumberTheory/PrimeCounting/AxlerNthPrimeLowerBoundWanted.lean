/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Nth

namespace MetaMathlibExt

@[expose] public section

/-- Axler's explicit lower bound for the `n`th prime (statement only).

For every integer `n ≥ 2`,
`pₙ > n * (log n + log log n - 1 + (log log n - 2) / log n -
((log log n) ^ 2 - 6 * log log n + 11.321) / (2 * (log n) ^ 2))`.

Mathlib's `Nat.nth Nat.Prime` is zero-indexed, so `Nat.nth Nat.Prime (n - 1)`
is the source's one-indexed `pₙ`; the hypothesis `2 ≤ n` makes the
subtraction `n - 1` safe. The inequality is strict and the decimal `11.321`
is kept exactly as stated.

Source: Christian Axler, "New Estimates for the nth Prime Number,"
Journal of Integer Sequences 22 (2019), Article 19.4.2, Theorem `thm104`,
equation (1.14), lines 190--196 of
https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex. -/
theorem_wanted axler_nth_prime_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (Real.log (n : ℝ) + Real.log (Real.log (n : ℝ)) - 1 +
      (Real.log (Real.log (n : ℝ)) - 2) / Real.log (n : ℝ) -
      ((Real.log (Real.log (n : ℝ))) ^ 2 - 6 * Real.log (Real.log (n : ℝ)) + 11.321) /
        (2 * (Real.log (n : ℝ)) ^ 2)) <
      (Nat.nth Nat.Prime (n - 1) : ℝ)

end

end MetaMathlibExt
