/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Chebyshev

/-!
# Prime number theorem error estimate for Chebyshev `θ` — wishlist

This file records a published quantitative prime-number-theorem error estimate.
-/

@[expose] public section

namespace MetaMathlibExt.PrimeNumberTheorem

open Asymptotics

/-- Quantitative prime number theorem for the Chebyshev `θ` function: for every
real `ε > 0`, `θ(x) - x = O(x * exp(-(log x)^(3/5 - ε)))` as `x → +∞`.

This is stronger than the qualitative Chebyshev-`θ` asymptotic equivalent to the
repository's existing prime-counting `prime_number_theorem`
(i.e. `θ(x) ~ x`, vanishing relative error with no rate), and it
and this exponential asymptotic error rate is distinct from the existing
explicit polynomial-in-`log x` Dusart bounds, some global and some finite-range.

Source: Julian Ransford, "A Sum of Gcd's over Friable Numbers", Journal of
Integer Sequences 19 (2016), Prime Number Theorem at lines 288–292;
URL: https://cs.uwaterloo.ca/journals/JIS/VOL19/Ransford/ransford2.tex
complete-source SHA-256
`1675f24c7dbb411a931a2c37a36917b63494686ad03d851beb2a18814e04005d`;
normalized contextual lines 288–292 SHA-256
`adb74cce8f0da6d1a60450de8ce1029a6e5de3c77e1d9b6a8de7d62dece7f8d5`;
normalized theorem lines 290–292 SHA-256
`2aa08383a1b0c24261c27687f2576878a793de5885ef2f1ac841eebe4cf480bb`. -/
public theorem_wanted prime_number_theorem_chebyshev_theta_error :
    ∀ epsilon : ℝ, 0 < epsilon →
      (fun x : ℝ => Chebyshev.theta x - x) =O[Filter.atTop]
        (fun x : ℝ => x * Real.exp (-(Real.rpow (Real.log x) ((3 / 5 : ℝ) - epsilon))))

end MetaMathlibExt.PrimeNumberTheorem
