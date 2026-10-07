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

/-- The Meissel–Mertens constant
`B = lim_{x → ∞} (∑_{p ≤ x} 1 / p - log log x) ≈ 0.2614972128`,
defined by its standard limiting characterization. -/
noncomputable def meisselMertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ =>
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      1 / (p : ℝ)) - Real.log (Real.log n))

/-- Dusart explicit Mertens second theorem: for `x ≥ 2278383`,
`∑_{p ≤ x} 1 / p = log log x + B + E` with `|E| ≤ 0.2 / (log x)^3`,
where `B` is the Meissel–Mertens constant. The sum ranges over
`Finset.range (⌊x⌋₊ + 1)` filtered by `Nat.Prime`.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.6. -/
theorem_wanted dusart_reciprocal_prime_sum (x : ℝ) (hx : 2278383 ≤ x) :
    ∃ E, ((∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)),
        1 / (p : ℝ))
      = Real.log (Real.log x) + meisselMertensConstant + E
      ∧ |E| ≤ 0.2 / (Real.log x) ^ 3)

end

end MetaMathlibExt
