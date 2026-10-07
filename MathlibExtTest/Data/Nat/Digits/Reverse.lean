/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Data.Nat.Digits.Reverse

example : Nat.reverseDigits 10 123 = 321 := by decide

example : Nat.reverseDigits 2 6 = 3 := by decide

example (n : ℕ) : Nat.reverseDigits 0 n = n := by simp

example (n : ℕ) : Nat.reverseDigits 1 n = n := by simp
