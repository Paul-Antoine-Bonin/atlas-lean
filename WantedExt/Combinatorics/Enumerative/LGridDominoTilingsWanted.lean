/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section

namespace MetaMathlibExt

/--
The Fibonacci formula for the number of domino tilings of the L-grid, together
with its specialization and Cassini-type identity.

Source: Roberto Tauraso, "A New Domino Tiling Sequence," Journal of Integer
Sequences 7 (2004), Article 04.2.3, Lemma (Section 2, equations Lformula and
Lcassini), lines 200–221,
https://cs.uwaterloo.ca/journals/JIS/VOL7/Tauraso/tauraso3.tex

With `f_0 = 0, f_1 = 1` (`Nat.fib`), the tiling count `L` is unfolded as the
Fibonacci expression `f_{n+1} f_m + f_n f_{m+1}`, so the first two conjuncts
are definitional; the substantive content is the Cassini-type identity
`L_{n,n-1}^2 = L_{n,n} L_{n-1,n-1} + 1` (checked for `2 ≤ n ≤ 11`).
-/
public theorem_wanted domino_tilings_L_grid_via_fibonacci :
    let L : ℕ → ℕ → ℕ := fun n m =>
      Nat.fib (n + 1) * Nat.fib m + Nat.fib n * Nat.fib (m + 1)
    let a : ℕ → ℕ := fun n =>
      Nat.fib (n + 1) * Nat.fib (n - 1) + Nat.fib n ^ 2
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      L n m = Nat.fib (n + 1) * Nat.fib m +
        Nat.fib n * Nat.fib (m + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → L n (n - 1) = a n) ∧
    (∀ n : ℕ, 2 ≤ n →
      (L n (n - 1)) ^ 2 = L n n * L (n - 1) (n - 1) + 1)

end MetaMathlibExt
