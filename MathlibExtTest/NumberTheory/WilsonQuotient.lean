/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.NumberTheory.WilsonQuotient

example : Int.wilsonQuotient 3 = 1 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : Int.wilsonQuotient 5 = 5 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : Int.wilsonQuotient 7 = 103 := by
  simp only [Int.wilsonQuotient, Nat.factorial]
  norm_num

example : (5 : ℤ) * Int.wilsonQuotient 5 = (Nat.factorial (5 - 1) : ℤ) + 1 :=
  Int.mul_wilsonQuotient 5 (by decide)

example : (Nat.factorial (5 - 1) : ℤ) = (5 : ℤ) * Int.wilsonQuotient 5 - 1 :=
  Int.factorial_eq_mul_wilsonQuotient_sub_one 5 (by decide)
