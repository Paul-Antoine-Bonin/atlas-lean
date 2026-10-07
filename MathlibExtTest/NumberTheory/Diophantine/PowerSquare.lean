/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Diophantine.PowerSquare
import Mathlib.Tactic.Linarith

example : 3 ^ (0 + 1) + 1 = 2 ^ 2 := by decide

example (y z : ℕ) (h : 3 ^ (y + 1) + 1 = z ^ 2) : y = 0 :=
  Nat.eq_zero_of_three_pow_succ_add_one_eq_sq h

example (z : ℕ) (h : 3 ^ (0 + 1) + 1 = z ^ 2) : z = 2 := by
  have hz2 : z ^ 2 = 4 := by omega
  nlinarith

example : ¬∃ z : ℕ, 3 ^ (1 + 1) + 1 = z ^ 2 := by
  rintro ⟨z, hz⟩
  have := Nat.eq_zero_of_three_pow_succ_add_one_eq_sq hz
  omega

example : ¬∃ z : ℕ, 3 ^ (2 + 1) + 1 = z ^ 2 := by
  rintro ⟨z, hz⟩
  have := Nat.eq_zero_of_three_pow_succ_add_one_eq_sq hz
  omega

example : ¬∃ z : ℕ, 3 ^ (3 + 1) + 1 = z ^ 2 := by
  rintro ⟨z, hz⟩
  have := Nat.eq_zero_of_three_pow_succ_add_one_eq_sq hz
  omega
