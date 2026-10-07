/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- No Collatz m-cycle with `m ≤ 91`.

`C` is the shortcut Collatz operator (`n/2` for even `n`, `(3n+1)/2` for
odd `n`); a cycle is nontrivial when every orbit entry exceeds 2 (the
trivial cycle is `1, 2, 1, 2, …`), has minimal period `p`, and is an
m-cycle when exactly `m` positions lie cyclically strictly below both
neighbours.

Source: Christian Hercher, "There are no Collatz m-Cycles with m ≤ 91,"
Journal of Integer Sequences 26 (2023), Article 23.3.5, Main Theorem
(label Theorem17), lines 541–543,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.tex
with the operator at lines 104–111 and the m-cycle definition at
lines 149–151. -/
public theorem_wanted no_collatz_m_cycle_le_ninety_one
    (m : ℕ) (hm : m ≤ 91) :
    ¬ ∃ n p : ℕ, 0 < p ∧
      (∀ i : ℕ, i < p →
        2 < (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n) ∧
      (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[p] n = n ∧
      (∀ k : ℕ, 0 < k → k < p →
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[k] n ≠ n) ∧
      (((Finset.range p).filter (fun i =>
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n <
          (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[(i + 1) % p] n ∧
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n <
          (fun c : ℕ => if c % 2 = 0 then c / 2 else
            (3 * c + 1) / 2)^[(i + p - 1) % p] n)).card = m)

end MetaMathlibExt
