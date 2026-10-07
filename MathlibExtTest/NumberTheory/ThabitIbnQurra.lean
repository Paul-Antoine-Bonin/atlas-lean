/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThabitIbnQurra

open scoped BigOperators

-- The classical `n = 2` case gives the amicable pair `220` and `284`.
example :
    220 < 284 ∧
      ∑ d ∈ Nat.properDivisors 220, d = 284 ∧
      ∑ d ∈ Nat.properDivisors 284, d = 220 := by
  simpa using
    (MetaMathlibExt.thabit_ibn_qurra 2 11 5 71 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
