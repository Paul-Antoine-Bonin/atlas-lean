/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperfactorialPartition

namespace MetaMathlibExt
def hyperfactorialPartitionZero : HyperfactorialPartition 0 where
  k := 0
  digits := Fin.elim0
  bound := by intro i; exact Fin.elim0 i
  normalized := by
    intro h
    exact (Nat.not_lt_zero 0 h).elim
  value := by decide

def hyperfactorialPartitionOne : HyperfactorialPartition 1 where
  k := 1
  digits := fun _ => 1
  bound := by decide
  normalized := by simp [HyperfactorialDigitsNormalized]
  value := by decide

def hyperfactorialPartitionTwo : HyperfactorialPartition 2 where
  k := 1
  digits := fun _ => 2
  bound := by decide
  normalized := by simp [HyperfactorialDigitsNormalized]
  value := by decide

example : ¬ (3 ≤ 2 * (0 + 1)) := by decide

example : ¬ HyperfactorialDigitsNormalized 2
    (fun i : Fin 2 => if i = 0 then 1 else 0) := by
  intro h
  simpa [HyperfactorialDigitsNormalized] using h (by decide)
end MetaMathlibExt
