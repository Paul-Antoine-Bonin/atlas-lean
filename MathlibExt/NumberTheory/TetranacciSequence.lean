/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Tetranacci sequence

This module defines the standard zero-indexed Tetranacci sequence, OEIS A000078.

Source: Tian-Xiao He, *Impulse Response Sequences and Construction of Number Sequence
Identities*, <https://cs.uwaterloo.ca/journals/JIS/VOL16/He/he13.tex>.

JIS concept: `jis_sem_f54f2461d2aa8ee887f170d6`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The Tetranacci sequence `0, 0, 0, 1, 1, 2, 4, 8, …` (OEIS A000078), in which
each term after the first four is the sum of its four predecessors. -/
def tetranacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 =>
      tetranacci (n + 3) + tetranacci (n + 2) + tetranacci (n + 1) + tetranacci n

end

end MetaMathlibExt
