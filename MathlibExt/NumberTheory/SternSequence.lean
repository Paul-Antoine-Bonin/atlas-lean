/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Stern sequence (`jis_term_8e87f9eebae5b6160acdc06a`, "Stern diatomic sequence",
OEIS A002487): the function `s : Nat → Nat` with `s 0 = 0`, `s 1 = 1`,
`s (2 * n) = s n` and `s (2 * n + 1) = s n + s (n + 1)` for `n ≥ 1`
(JIS Lansing, lines 92-103; JIS Dennison, lines 80-85). -/
def sternSequence : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then sternSequence ((n + 2) / 2)
    else sternSequence ((n + 2) / 2) + sternSequence ((n + 2) / 2 + 1)
termination_by n => n
decreasing_by all_goals omega

/-- `sternSequence 0 = 0` (Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`,
OEIS A002487; JIS Lansing, lines 92-103). -/
theorem stern_zero : sternSequence 0 = 0 := by
  simp only [sternSequence]

/-- `sternSequence 1 = 1` (Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`,
OEIS A002487; JIS Lansing, lines 92-103). -/
theorem stern_one : sternSequence 1 = 1 := by
  simp only [sternSequence]

/-- Even recurrence `sternSequence (2 * n) = sternSequence n` for `n ≥ 1`
(Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487;
JIS Lansing, lines 92-103; JIS Dennison, lines 80-85). -/
theorem stern_even (n : Nat) (hn : 1 ≤ n) : sternSequence (2 * n) = sternSequence n := by
  have h2 : 2 * n = ((2 * n - 2) + 2) := by omega
  rw [h2]
  have hmod : (((2 * n - 2) + 2) % 2) = 0 := by omega
  have hdiv : (((2 * n - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_left hmod, hdiv]

/-- Odd recurrence `sternSequence (2 * n + 1) = sternSequence n + sternSequence (n + 1)`
for `n ≥ 1` (Stern sequence `jis_term_8e87f9eebae5b6160acdc06a`, OEIS A002487;
JIS Lansing, lines 92-103; JIS Dennison, lines 80-85). -/
theorem stern_odd (n : Nat) (hn : 1 ≤ n) :
    sternSequence (2 * n + 1) = sternSequence n + sternSequence (n + 1) := by
  have h2 : 2 * n + 1 = (((2 * n + 1) - 2) + 2) := by omega
  rw [h2]
  have hne : (((2 * n + 1) - 2) + 2) % 2 ≠ 0 := by omega
  have hdiv : ((((2 * n + 1) - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_right hne, hdiv]

end

end MetaMathlibExt
