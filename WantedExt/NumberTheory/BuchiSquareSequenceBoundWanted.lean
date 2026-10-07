/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.BuchiSquareSequenceBoundWanted

/-- A length-`M` integer Büchi sequence: the second differences of the squared
terms are constantly `2`. Only the prefix `j < M` of the total function `u`
is observed. -/
def IsBuchiSequence (M : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j : ℕ, j + 2 < M →
    u (j + 2) ^ 2 - 2 * u (j + 1) ^ 2 + u j ^ 2 = 2

/-- A length-`M` Büchi sequence is trivial when, up to independently changing
the signs of its terms, it is a run of consecutive increasing integers. Since
independent signs do not change squares, and equality of integer squares
supplies the necessary signs, this is encoded by requiring an integer `x`
with `u j ^ 2 = (x + j) ^ 2` for every `j < M`. -/
def IsTrivial (M : ℕ) (u : ℕ → ℤ) : Prop :=
  ∃ x : ℤ, ∀ j : ℕ, j < M →
    u j ^ 2 = (x + (j : ℤ)) ^ 2

/-- Büchi's integer-square sequence conjecture in general existential-length
form: there exists a length `M ≥ 5` for which every length-`M` Büchi sequence
is trivial. -/
def conjecture : Prop :=
  ∃ M : ℕ, 5 ≤ M ∧
    ∀ u : ℕ → ℤ, IsBuchiSequence M u → IsTrivial M u

/--
Resolved true: Stanley Yao Xiao (arXiv:2412.16740v3, Jun 2025) proves unconditionally that five
integer squares with constant second difference 2 are consecutive (Theorem 1.3), so the
formalized existential-length claim holds with M = 5; the earlier length-8 bound was Vojta's
conditional result under Bombieri-Lang. Source: Stanley Yao Xiao, Hilbert's tenth problem for
systems of diagonal quadratic forms, and Büchi's problem, arXiv:2412.16740v3 (2025),
https://arxiv.org/abs/2412.16740v3. Moved from
`OpenConjectures/NumberTheory/BuchiSquareSequenceBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.BuchiSquareSequenceBoundWanted
