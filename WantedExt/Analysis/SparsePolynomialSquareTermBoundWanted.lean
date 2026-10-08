/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Term counts in squares of polynomials
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.SparsePolynomialSquareTermBoundWanted

/-- For every positive target `k`, sufficiently many nonzero terms in a complex polynomial force
its square to have at least `k` nonzero terms. -/
def conjecture : Prop :=
  ∃ f : ℕ → ℕ,
    ∀ k : ℕ, 0 < k →
      ∀ p : Polynomial ℂ,
        f k ≤ p.support.card → k ≤ (p ^ 2).support.card

/--
Resolved true: Schinzel (Acta Arith. 49 (1987) 55-70) proved the Erdős-Rényi conjecture that the
number of terms of g in C[x] is bounded in terms of that of g^2; Fuchs-Mantova-Zannier
(arXiv:1412.4548, Thm 1.1) give a uniform version. This yields the threshold f(k). Source: C.
Fuchs, V. Mantova and U. Zannier, On fewnomials, integral points and a toric version of
Bertini's theorem (2017), arXiv:1412.4548, https://arxiv.org/abs/1412.4548. Moved from
`OpenConjectures/Analysis/SparsePolynomialSquareTermBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.SparsePolynomialSquareTermBoundWanted
