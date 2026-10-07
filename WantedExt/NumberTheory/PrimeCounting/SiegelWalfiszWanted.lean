/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi

/-!
# Siegel–Walfisz theorem — wishlist

This file records a uniform residue-class von Mangoldt estimate.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting.SiegelWalfiszWanted

/-- For each positive real exponent `N`, the Siegel–Walfisz estimate holds
uniformly for positive moduli `q ≤ (log x)^N` and reduced residue classes.

The constants may depend on `N`, but not on `x`, `q`, or `a`.

Source: P. Holdridge, *Random Diophantine Equations in the Primes*,
arXiv:2305.06306v2, Theorem 4.2, citing H. Davenport, *Multiplicative Number
Theory*, 2nd ed., revised by H. L. Montgomery, Springer, 1980, Chapter 22. -/
public theorem_wanted siegel_walfisz (N : ℝ) (hN : 0 < N) :
    ∃ (c C X₀ : ℝ), 0 < c ∧ 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
        ∀ q : ℕ, 0 < q →
          ∀ a : ZMod q, IsUnit a →
            (q : ℝ) ≤ (Real.log x) ^ N →
              |Chebyshev.psiResidueClass a x - x / (Nat.totient q : ℝ)| ≤
                C * x * Real.exp (-c * Real.sqrt (Real.log x))

end MathlibExt.NumberTheory.PrimeCounting.SiegelWalfiszWanted
