/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import MathlibExt.Combinatorics.Enumerative.Partition.Landau

open Nat

variable {n : ℕ}

example (p : n.Partition) : p.partsLCM = p.parts.lcm :=
  rfl

example (p : n.Partition) : p.partsLCM ≤ landauFunction n :=
  Partition.partsLCM_le_landauFunction p

example (n : ℕ) : ∃ p : n.Partition, p.partsLCM = landauFunction n :=
  exists_partition_partsLCM_eq_landauFunction n

example : landauFunction 0 = 1 := by simp

example : landauFunction 1 = 1 := by simp

set_option linter.hashCommand false in
#guard landauFunction 5 = 6
