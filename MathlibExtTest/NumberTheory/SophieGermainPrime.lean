/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SophieGermainPrime

-- `2` is prime and `2 * 2 + 1 = 5` is prime.
example : Nat.IsSophieGermainPrime 2 := by
  rw [Nat.isSophieGermainPrime_iff]
  decide

-- `3` is prime and `2 * 3 + 1 = 7` is prime.
example : Nat.IsSophieGermainPrime 3 := by
  rw [Nat.isSophieGermainPrime_iff]
  decide

-- `5` is prime and `2 * 5 + 1 = 11` is prime.
example : Nat.IsSophieGermainPrime 5 := by
  rw [Nat.isSophieGermainPrime_iff]
  decide

-- `7` is prime but `2 * 7 + 1 = 15` is not prime.
example : ¬ Nat.IsSophieGermainPrime 7 := by
  rw [Nat.isSophieGermainPrime_iff]
  decide

-- Characterization via the definitional iff on the witness values.
example : Nat.IsSophieGermainPrime 2 ↔ Nat.Prime 2 ∧ Nat.Prime 5 :=
  Nat.isSophieGermainPrime_iff 2

example : Nat.IsSophieGermainPrime 7 ↔ Nat.Prime 7 ∧ Nat.Prime 15 :=
  Nat.isSophieGermainPrime_iff 7
