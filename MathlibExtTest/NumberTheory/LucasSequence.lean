/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

example : fibonacciLucasParams.p = 1 := rfl
example : fibonacciLucasParams.q = -1 := rfl
example : fibonacciLucasParams.q ≠ 0 := fibonacciLucasParams.q_ne_zero
example : fibonacciLucasParams.IsCoprime := ⟨1, 0, by decide⟩

example : lucasU fibonacciLucasParams 0 = 0 := rfl
example : lucasU fibonacciLucasParams 1 = 1 := rfl
example : lucasU fibonacciLucasParams 5 = 5 := by decide
example : lucasV fibonacciLucasParams 0 = 2 := rfl
example : lucasV fibonacciLucasParams 1 = 1 := rfl
example : lucasV fibonacciLucasParams 5 = 11 := by decide
example : lucasNumber 5 = 11 := rfl

example (n : ℕ) : lucasU fibonacciLucasParams n = (Nat.fib n : ℤ) :=
  lucasU_fibonacciLucasParams n

example (n : ℕ) : lucasV fibonacciLucasParams n = (lucasNumber n : ℤ) :=
  lucasV_fibonacciLucasParams n

end MetaMathlibExt
