/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Octagonal pyramidal numbers

The enumerative interpretation comes from Milan Janjić, *Binomial
Coefficients and Enumeration of Restricted Words*, Journal of Integer
Sequences 19 (2016), Article 16.7.3.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- The `k`-th octagonal pyramidal number, `k(k+1)(2k-1)/2`. -/
def octagonalPyramidalNumber (k : ℕ) : ℕ :=
  k * (k + 1) * (2 * k - 1) / 2

/-- Ordered compositions of `k + 14` into `k` positive parts, with no part
equal to `2`, `3`, or `4`.

Stable source identifiers: concept `jis_sem_775e702cd81d5e5e2661ccc9`,
statement `jis_4f77f6102ca88eba755447c5`.
-/
def octagonalPyramidalCompositions (k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 (k + 14) \ {2, 3, 4}).filter
    fun c => ∑ i, c i = k + 14

end

end MetaMathlibExt
