/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting

/-!
# Labos primes

This file formalizes Definition 2 from Vladimir Shevelev,
*Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- `IsLabosPrime n L` says that `L` is the least positive integer satisfying
`π(L) - π(L / 2) = n`, for `n ≥ 1`. -/
def IsLabosPrime (n L : ℕ) : Prop :=
  1 ≤ n ∧ 0 < L ∧ Nat.primeCounting L - Nat.primeCounting (L / 2) = n ∧
    ∀ m, 0 < m → m < L → Nat.primeCounting m - Nat.primeCounting (m / 2) ≠ n

end MetaMathlibExt
