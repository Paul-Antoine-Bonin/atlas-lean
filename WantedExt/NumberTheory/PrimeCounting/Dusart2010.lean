/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Batteries.Util.ProofWanted

@[expose] public section

/-- Pierre Dusart, arXiv:1002.0442v1, Proposition at source lines 549--552;
stable ID `lead:dusart-2010-prime-interval:aee139bd68`. -/
theorem_wanted dusart_2010_prime_interval_bound :
    ∀ (x : ℝ), 396738 ≤ x →
      ∃ (p : ℕ), Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x) ^ 2))

/-!
## Explicit prime-counting bounds

The PNT repository records the following results as `Dusart.corollary_5_2_d`
and `Dusart.corollary_5_2_c`, with its `pi x` defined as
`Nat.primeCounting ⌊x⌋₊`. Both proofs remain `sorry` there.

Source: Pierre Dusart, "Explicit estimates of some functions over primes,"
*The Ramanujan Journal* 45 (2018), 227-251, Corollary 5.2(c,d),
<https://doi.org/10.1007/s11139-016-9839-4>.

Lean mirror: `PrimeNumberTheoremAnd/IEANTN/Dusart.lean`, lines 248-268,
revision `a5154676af9aa3095150ee410cdda80555aa0642`; source-span SHA-256
`8b6cb3655e067df7fbf79fd6644be6780948bc144a1abb471cdfa7204322c4d6`.
-/

/-- Dusart's explicit upper bound for the prime-counting function, Corollary 5.2(d). -/
public theorem_wanted dusart_pi_upper : ∀ x : ℝ, 1 < x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      x / Real.log x * (1 + 1.2762 / Real.log x)

/-- Dusart's explicit lower bound for the prime-counting function, Corollary 5.2(c). -/
public theorem_wanted dusart_pi_lower : ∀ x : ℝ, 599 ≤ x →
    x / Real.log x * (1 + 1 / Real.log x) ≤
      (Nat.primeCounting ⌊x⌋₊ : ℝ)

end
