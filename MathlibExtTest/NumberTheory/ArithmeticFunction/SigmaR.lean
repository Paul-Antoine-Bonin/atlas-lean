/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SigmaR

/-!
# Tests for complex-exponent divisor sums
-/

@[expose] public section

open ArithmeticFunction

example (s : ℂ) : sigmaR s 0 = 0 := by
  simp

example (s : ℂ) : sigmaR s 1 = 1 := by
  simp

example (k n : ℕ) : sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  exact sigmaR_natCast_apply k n

example (n : ℕ) : sigmaR (0 : ℂ) n = (n.divisors.card : ℂ) := by
  exact sigmaR_zero_apply n
