/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Erdős Problem 793: growth of the largest 2-primitive family.

Let `F(n)` be the maximum size of a set `A ⊆ {1, …, n}` such that
no element divides the product of two others: `¬ a ∣ b * c`
whenever `a, b, c ∈ A` with `a ≠ b` and `a ≠ c`.
Is there a constant `C` with
`F(n) = π(n) + (C + o(1)) * n^(2/3) / (log n)^2`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted

/-! Source record `EP-793`. -/

/-- A finite set of naturals is good when no element divides the product of
any two other (not necessarily distinct from each other) elements, and every
element is positive. -/
def Good (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c) ∧ (∀ a ∈ A, 1 ≤ a)

/-- `F(n)`: the maximum cardinality of a good subset of `{1, …, n}`,
as the supremum of all sizes attained by good subsets. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ Good A ∧ A.card = k}

/-- Erdős Problem 793: there is a positive constant `C` such that the excess
of `F(n)` over `π(n)`, normalized by `n^(2/3) / (log n)^2`, tends to `C`.
The difference is taken in `ℤ` before casting to `ℝ`. At `n = 0, 1` the
ratio is junk (`log n ≤ 0`, division by zero), which is well-formed and
irrelevant to the limit at infinity. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ Filter.Tendsto
    (fun n : ℕ => (((F n : ℤ) - (Nat.primeCounting n : ℤ)) : ℝ) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2))
    Filter.atTop (nhds C)

/--
Resolved true: Chojecki (arXiv:2607.15306, 2026), Theorem 1.1, proves
F(n)=π(n)+(27/2+o(1))n^(2/3)/(log n)^2 for sets with a∤bc whenever a∉{b,c}, b=c allowed, which
is the Lean Good predicate; so the target holds with C=27/2. Source: P. Chojecki, The Second
Term for Strongly 2-Primitive Sets, arXiv preprint (2026), arXiv:2607.15306,
https://arxiv.org/abs/2607.15306. Moved from
`OpenConjectures/NumberTheory/ErdosDivisibilityFamilyGrowth`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted
