/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Erdős Problem 152: for any `M ≥ 1`, every sufficiently large finite Sidon set
`A ⊆ ℕ` has at least `M` sums `a ∈ A + A` isolated from the rest of the
sumset, i.e. with `a + 1 ∉ A + A` and `a - 1 ∉ A + A`.

Formalization note: since sums are naturals, `a - 1` uses truncated
subtraction and the predecessor condition is stated as `a = 0 ∨ a - 1 ∉ S`,
which is vacuously true at `a = 0` (where `0` has no predecessor in `ℕ`)
and is the true predecessor condition for `a ≥ 1`. This also keeps the
isolated-sum predicate decidable (an unbounded `∀ p : ℕ` predecessor
quantifier would not be).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted

/-! Source record `EP-152`. -/

/-- A finite set of naturals is Sidon: the canonical `Set.IsSidon`
predicate from `MathlibExt` applied to its coercion to a set. -/
def IsSidon (A : Finset ℕ) : Prop :=
  Set.IsSidon (A : Set ℕ)

/-- The sumset `A + A` as a finset: all values `x + y` with `x, y ∈ A`. -/
def Sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

/-- A sum `a ∈ S` is isolated when neither neighbor lies in `S`. The
predecessor condition uses truncated subtraction with the `a = 0` case
vacuous, since `0` has no predecessor in `ℕ`. -/
def IsIsolated (S : Finset ℕ) (a : ℕ) : Prop :=
  a ∈ S ∧ a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S)

/-- Number of isolated sums in `S`. -/
def IsolatedCount (S : Finset ℕ) : ℕ :=
  (S.filter (fun a => a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S))).card

/-- [EP-152] For any `M ≥ 1`, every sufficiently large finite Sidon set has at
least `M` isolated sums in its sumset. -/
def conjecture : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    ∃ K : ℕ, ∀ A : Finset ℕ,
      IsSidon A → K ≤ A.card → M ≤ IsolatedCount (Sumset A)

/--
Resolved true: Tsoukalas et al. (Google DeepMind, arXiv:2605.22763, 2026, Erdős #152 theorem,
with a Lean proof) show every Sidon set A ⊂ N of size n has at least (n^2-100n-16)/16 isolated
elements in A+A, so large finite Sidon sets have arbitrarily many isolated sums. Source: George
Tsoukalas et al., Advancing Mathematics Research with AI-Driven Formal Proof Search, arXiv
preprint (2026), arXiv:2605.22763, https://arxiv.org/abs/2605.22763. Moved from
`OpenConjectures/Combinatorics/ErdosSidonIsolatedSums`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted
