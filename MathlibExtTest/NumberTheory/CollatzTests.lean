/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Collatz

@[expose] public section

example : Nat.collatzStep 6 = 3 := by decide

example : Nat.collatzStep 3 = 10 := by decide

example : Nat.collatzIterate 3 6 = 5 := by decide

example : Nat.collatzStoppingTime 1 = some 0 := by
  have h : ∃ k : ℕ, Nat.collatzIterate k 1 = 1 := ⟨0, rfl⟩
  simp [Nat.collatzStoppingTime, h, Nat.collatzIterate]
