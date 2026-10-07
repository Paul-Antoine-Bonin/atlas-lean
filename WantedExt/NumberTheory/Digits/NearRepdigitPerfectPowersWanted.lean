/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace MetaMathlibExt

/-!
# Near-repdigit perfect powers

Finiteness of perfect `l`-th powers whose decimal digits are all equal but one.
-/

/--
For fixed `l ≥ 3`, there are only finitely many perfect `l`-th powers all of
whose decimal digits are equal but one, except for the trivial families
`10 ^ (l * n)` and, for `l = 3`, `8 * 10 ^ (3 * n)`.

Source: Omar Kihel and Florian Luca, "Perfect Powers with All Equal Digits
but One," Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem 1
(label thm:1), lines 134–140,
https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex.

The digit condition says some digit `c < 10` occurs in `Nat.digits 10 y`
with exactly one digit different from `c`.
-/
public theorem_wanted finite_near_repdigit_perfect_powers (l : ℕ) (hl : 3 ≤ l) :
  Set.Finite
    { y : ℕ | (∃ x : ℕ, y = x ^ l) ∧
    (∃ c : ℕ, c < 10 ∧ c ∈ Nat.digits 10 y ∧
    (List.filter (fun a => a != c) (Nat.digits 10 y)).length = 1) ∧ ¬
    ((∃ n : ℕ, y = 10 ^ (l * n)) ∨ (l = 3 ∧ ∃ n : ℕ, y = 8 * 10 ^ (3 * n))) }

end MetaMathlibExt
