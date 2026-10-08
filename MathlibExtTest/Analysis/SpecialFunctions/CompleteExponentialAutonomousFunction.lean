/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.CompleteExponentialAutonomousFunction

namespace MetaMathlibExt

example (x : ℕ → ℂ) : completeBellPolynomial 0 x = 1 := by
  rw [completeBellPolynomial_zero]
example (x : ℕ → ℂ) : completeBellPolynomial 1 x = x 0 := by
  rw [completeBellPolynomial_one]
example (x : ℕ → ℂ) : completeBellPolynomial 2 x = x 0 ^ 2 + x 1 := by
  rw [completeBellPolynomial_two]

example (a : ℂ) (x : Fin 1 → ℂ) :
    completeExponentialAutonomousFunction 1 (by decide) a x 0 = x 0 := by
  rw [completeExponentialAutonomousFunction, Nat.strongRecOn_eq]
  simp

example (a : ℂ) (x : Fin 1 → ℂ) :
    completeExponentialAutonomousFunction 1 (by decide) a x 1 =
      a * Complex.exp (x 0) := by
  rw [completeExponentialAutonomousFunction, Nat.strongRecOn_eq]
  simp

example (a : ℂ) (x : Fin 1 → ℂ) :
    completeExponentialAutonomousFunction 1 (by decide) a x 2 =
      (a * Complex.exp (x 0)) ^ 2 := by
  rw [completeExponentialAutonomousFunction, Nat.strongRecOn_eq]
  norm_num
  rw [Nat.strongRecOn_eq]
  simp
  ring

end MetaMathlibExt
