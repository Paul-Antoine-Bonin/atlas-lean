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

/-- Dusart shifted-log lower bound for `π(x)`: for `x ≥ 5393`,
`π(x) ≥ x / (log x - 1)`, with `π` as `Nat.primeCounting ⌊x⌋₊`.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Corollary 5.3(a). -/
theorem_wanted dusart_pi_lower_shifted_log (x : ℝ) (hx : 5393 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≥ x / (Real.log x - 1)

end

end MetaMathlibExt
