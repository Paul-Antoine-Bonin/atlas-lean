/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BellWeakExcedance

-- The weak-excedance count for n = 3 is 5.
example :
    Fintype.card { σ : Equiv.Perm (Fin 3) //
      ∀ i j : Fin 3, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = 5 := by
  rw [MetaMathlibExt.bell_count_perm_increasing_weakExcedance_letters]
  simp [Nat.bell_succ, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]

-- The weak-excedance count for n = 4 is 15.
example :
    Fintype.card { σ : Equiv.Perm (Fin 4) //
      ∀ i j : Fin 4, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = 15 := by
  rw [MetaMathlibExt.bell_count_perm_increasing_weakExcedance_letters]
  simp [Nat.bell_succ, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
