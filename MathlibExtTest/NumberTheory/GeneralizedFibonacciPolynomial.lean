/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import Mathlib.Tactic

namespace MetaMathlibExt

example : generalizedFibonacciPolynomial 2 3 5 7 0 = (2 : Polynomial ℤ) := by simp

example : generalizedFibonacciPolynomial 2 3 5 7 1 = (3 : Polynomial ℤ) := by simp

example : generalizedFibonacciPolynomial 2 3 5 7 2 = (29 : Polynomial ℤ) := by norm_num

example : generalizedFibonacciPolynomial 2 3 5 7 3 = (166 : Polynomial ℤ) := by norm_num

example (p0 p1 d g : Polynomial ℤ) (n : ℕ) :
    generalizedFibonacciPolynomial p0 p1 d g (n + 2) =
      d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
        g * generalizedFibonacciPolynomial p0 p1 d g n := by simp

end MetaMathlibExt
