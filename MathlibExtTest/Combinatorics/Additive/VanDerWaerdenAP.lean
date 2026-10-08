/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenAP

-- The finite interval theorem yields the infinite form for colorings of `ℕ`.
example (r k : Nat) (hr : 0 < r) (hk : 0 < k) (c : Nat → Fin r) :
    ∃ a d : Nat, 1 ≤ a ∧ 1 ≤ d ∧ ∀ i : Nat, i < k → c (a + i * d) = c a := by
  obtain ⟨N, hN⟩ := MetaMathlibExt.vanDerWaerden r k hr hk
  obtain ⟨a, d, ha, hd, hend, hmono⟩ := hN fun m ↦ c m
  refine ⟨a, d, ha, hd, ?_⟩
  intro i hi
  have h₁ : 1 ≤ a + i * d := by omega
  have h₂ : a + i * d ≤ N := by
    calc
      a + i * d ≤ a + (k - 1) * d := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_sub_one_of_lt hi)) a
      _ ≤ N := hend
  exact hmono i hi h₁ h₂ ⟨ha, by omega⟩
