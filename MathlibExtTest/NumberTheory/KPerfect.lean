/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KPerfect

example : Nat.IsKPerfect 2 6 := by
  rw [Nat.IsKPerfect]
  decide

example : Nat.IsKPerfect 3 120 := by
  rw [Nat.IsKPerfect]
  decide

example : ¬Nat.IsKPerfect 2 0 := by
  simp [Nat.IsKPerfect]

example : ¬Nat.IsKPerfect 0 6 := by
  rw [Nat.IsKPerfect]
  decide

example {k n : ℕ} (h : Nat.IsKPerfect k n) : 0 < k :=
  h.pos_k

example (n : ℕ) : Nat.IsKPerfect 2 n ↔ n.Perfect :=
  Nat.isKPerfect_two_iff n
