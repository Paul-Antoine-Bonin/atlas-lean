/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NewtonSequence

namespace MetaMathlibExt

example {R : Type*} [CommSemiring R] (a c : ℕ → R) (h : IsNewtonSequence a c) :
    a 1 = c 1 := by
  simpa using h.eq_recurrence 0

example {R : Type*} [CommSemiring R] (a c : ℕ → R) (h : IsNewtonSequence a c) :
    a 2 = a 1 * c 1 + 2 * c 2 := by
  simpa [Finset.range_one] using h.eq_recurrence 1

end MetaMathlibExt
