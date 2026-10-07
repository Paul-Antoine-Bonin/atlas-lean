/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- Dusart's constant for the log-weighted prime sum in Theorem 5.7, defined
by its standard limiting characterization. -/
noncomputable def mertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ =>
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      Real.log p / (p : ℝ)) - Real.log n)

/-- Dusart explicit Mertens first theorem: for `x ≥ 912560`,
`∑_{p ≤ x} log p / p = log x + M + E` with `|E| ≤ 0.3 / (log x)^2`,
where `M` is the Theorem 5.7 constant. The sum ranges over
`Finset.range (⌊x⌋₊ + 1)` filtered by `Nat.Prime`.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.7. -/
theorem_wanted dusart_log_prime_sum (x : ℝ) (hx : 912560 ≤ x) :
    ∃ E, ((∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)),
        Real.log p / (p : ℝ))
      = Real.log x + mertensConstant + E
      ∧ |E| ≤ 0.3 / (Real.log x) ^ 2)

end

end MetaMathlibExt
