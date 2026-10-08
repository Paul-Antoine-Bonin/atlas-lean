/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.AndrewsMacMahonPartition

namespace MetaMathlibExt

-- MacMahon's case at `n = 6` follows by specializing Andrews' theorem to `r = 1`.
example (r n : ℕ) (hr : r = 1) (hn : n = 6) :
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd (p.parts.count m) → 2 * r + 1 ≤ p.parts.count m } =
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1 } := by
  subst r
  subst n
  exact andrews_macmahon_partition_identity 1 6

end MetaMathlibExt
