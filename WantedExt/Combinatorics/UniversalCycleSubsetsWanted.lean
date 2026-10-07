/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.UniversalCycleSubsetsWanted

/-!
# Universal cycle conjecture for k-subsets

Source [AMR-030-0078]: Chung/Diaconis/Graham as cited in Cooper,
Combinatorial Problems I Like (2020 snapshot), Words and Codes,
source-order bullet 78.
Source URL: https://people.math.sc.edu/cooper/combprob.html

Clause list from the source:
* for each `k`;
* every sufficiently large `n`, i.e. `∃ N, ∀ n ≥ N, …`;
* with `k` dividing `((n - 1).choose (k - 1))`;
* there is a universal cycle for the `k`-subsets of an `n`-set, i.e. a cyclic
  sequence of length `n.choose k` over the `n`-set whose blocks of `k`
  consecutive cyclic entries yield each `k`-subset exactly once.
-/

/-- Universal cycle for the `k`-subsets of an `n`-set, in the sense of
Chung/Diaconis/Graham as cited in Cooper, Combinatorial Problems I Like,
Words and Codes bullet 78 [AMR-030-0078]: a cyclic sequence `c` of length
`Nat.choose n k` over `Fin n` such that every block of `k` consecutive cyclic
entries has cardinality `k` and every `k`-subset of `Fin n` occurs as such a
block for exactly one starting position. -/
def IsUniversalCycle (n k : ℕ) (c : Fin (Nat.choose n k) → Fin n) : Prop :=
  ∀ hpos : 0 < Nat.choose n k,
    (∀ i : Fin (Nat.choose n k),
      ((Finset.univ : Finset (Fin k)).image (fun j : Fin k =>
        c ⟨(i.val + j.val) % Nat.choose n k,
          Nat.mod_lt (i.val + j.val) hpos⟩)).card = k)
    ∧ ∀ S : Finset (Fin n), S.card = k →
        ∃! i : Fin (Nat.choose n k),
          (Finset.univ : Finset (Fin k)).image (fun j : Fin k =>
            c ⟨(i.val + j.val) % Nat.choose n k,
              Nat.mod_lt (i.val + j.val) hpos⟩) = S

/-- Chung/Diaconis/Graham universal-cycle conjecture as stated in Cooper,
Combinatorial Problems I Like, Words and Codes bullet 78 [AMR-030-0078]:
for each `k`, every sufficiently large `n` with `k ∣ Nat.choose (n - 1) (k - 1)`
admits a universal cycle for the `k`-subsets of an `n`-set. -/
def conjecture : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    k ∣ Nat.choose (n - 1) (k - 1) →
    ∃ c : Fin (Nat.choose n k) → Fin n, IsUniversalCycle n k c

/--
Resolved true: Resolved affirmatively: Glock, Joos, Kuehn and Osthus, Euler tours in
hypergraphs, Combinatorica 40 (2020), Theorem 1.1 proves that for each fixed k >= 2 and all
sufficiently large n satisfying k | C(n-1,k-1), the complete k-uniform hypergraph has a tight
Euler tour, exactly the universal cycle encoded here; the k = 1 case is elementary and the k = 0
branch is vacuous. Source: Stefan Glock, Felix Joos, Daniela Kühn, Deryk Osthus, Euler tours in
hypergraphs, Combinatorica 40 (2020), 679-690; arXiv:1808.07720,
https://arxiv.org/abs/1808.07720. Moved from
`OpenConjectures/Combinatorics/UniversalCycleSubsets`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.UniversalCycleSubsetsWanted
