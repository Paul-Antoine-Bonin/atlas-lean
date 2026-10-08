/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : gibonacciNumber 3 4 5 = 29 := by
  norm_num [gibonacciNumber]

example : gibonacciNumber 0 1 8 = 21 := by
  norm_num [gibonacciNumber]

example (n : ℕ) : gibonacciNumber 0 1 n = (Nat.fib n : ℤ) :=
  gibonacci_zero_one_eq_fib n

#print axioms gibonacciNumber
#print axioms gibonacci_zero_one_eq_fib

end MetaMathlibExt
