/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

namespace MetaMathlibExt

@[expose] public section

/-- Dusart second-order upper bound for `π(x)`: for `x > 1`,
`π(x) ≤ x / log x * (1 + 1 / log x + 2.53816 / (log x)^2)`, with `π` as
`Nat.primeCounting ⌊x⌋₊`.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Corollary 5.2(f). -/
theorem_wanted dusart_pi_upper_second_order (x : ℝ) (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
      ≤ x / Real.log x * (1 + 1 / Real.log x + 2.53816 / (Real.log x) ^ 2)

end

end MetaMathlibExt
