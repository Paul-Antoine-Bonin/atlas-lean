/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted

/-!
# Uniform prime counting in arithmetic progressions — wishlist

This file records a prime-counting form of the Siegel–Walfisz theorem.
-/

/-- Fix `B > 0`. Uniformly over positive moduli `q ≤ (log x) ^ B` and reduced
residue classes `b`, the number of primes `p ≤ x` congruent to `b` modulo `q`
differs from `li(x) / φ(q)` by at most `C * x * exp (-c * sqrt (log x))` for
sufficiently large `x`. The constants may depend on `B`, but not on `x`, `q`, or `b`.

The count uses `Nat.floor x` so its endpoint is inclusive. The logarithmic integral
is written explicitly as in the source, rather than using the principal-value
normalization `Real.logarithmicIntegral`.

Source: A. Guo, *Exceptional sets for compositions involving Euler's function, the
divisor-sum function and Dedekind's function*, arXiv:2608.19972v1, Lemma
`siegel`, `main.tex` lines 289–295. The official arXiv source file has SHA-256
`b4996cf07cc79703901e7313202c5a795b6e5313745490e0224d3589ff2a2d07`.
-/
public theorem_wanted uniform_prime_counting_arithmetic_progression (B : ℝ) (hB : 0 < B) :
    ∃ (c C X₀ : ℝ), 0 < c ∧ 0 < C ∧ 2 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
        ∀ q b : ℕ, 0 < q → Nat.Coprime b q →
          (q : ℝ) ≤ (Real.log x) ^ B →
            |(((Finset.range (Nat.floor x + 1)).filter fun p =>
                Nat.Prime p ∧ Nat.ModEq q p b).card : ℝ) -
              (∫ u in (2 : ℝ)..x, (Real.log u)⁻¹) / (Nat.totient q : ℝ)| ≤
                C * x * Real.exp (-c * Real.sqrt (Real.log x))

end MathlibExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted
