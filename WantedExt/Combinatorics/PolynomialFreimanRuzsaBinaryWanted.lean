/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial Freiman–Ruzsa conjecture over binary vector spaces

`OWR-12177-008`: a doubling set in `𝔽₂ⁿ` contains a large subset with
polynomially bounded span.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted

/-! Source: UnsolvedMath record `OWR-12177-008`, numeric id 30002239.
Complexity Theory (2013), Oberwolfach Reports,
DOI 10.4171/owr/2012/54, pp. 3267--3304. -/

/-- Polynomial Freiman–Ruzsa conjecture over binary vector spaces
([OWR-12177-008]): for doubling parameter `K ≥ 1`, polynomials `P Q`
independent of `n`, `A`, `K` witness that every nonempty `A : Finset 𝔽₂ⁿ`
with `|A + A| ≤ K * |A|` has a subset `A'` with `|A| / P(K) ≤ |A'|` and
`|span(A')| ≤ Q(K) * |A'|`. Resolved (true): proved by Gowers, Green,
Manners, and Tao (arXiv:2311.05762); stated as a proposition here. -/
def conjecture : Prop :=
  ∃ P Q : Polynomial ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < P.eval K ∧ 0 < Q.eval K) ∧
    ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (K : ℝ),
      1 ≤ K →
      A.Nonempty →
      ((((A.product A).image (fun p => p.1 + p.2)).card : ℝ)) ≤ K * (A.card : ℝ) →
      ∃ A' : Finset (Fin n → ZMod 2), A' ⊆ A ∧
        (A.card : ℝ) / P.eval K ≤ (A'.card : ℝ) ∧
        (Nat.card ↥(Submodule.span (ZMod 2) (↑A' : Set (Fin n → ZMod 2))) : ℝ) ≤
          Q.eval K * (A'.card : ℝ)

/--
Resolved true: Proved by Gowers, Green, Manners, and Tao (arXiv:2311.05762, November 2023): the
polynomial Freiman-Ruzsa conjecture in characteristic 2 (Marton's conjecture over F_2^n). Their
polynomial coset-cover result implies this large-subset polynomial-span formulation via the
densest-coset argument. Source: W. T. Gowers, B. Green, F. Manners, T. Tao, On a conjecture of
Marton, arXiv:2311.05762 (November 2023), https://arxiv.org/abs/2311.05762. Moved from
`OpenConjectures/Combinatorics/PolynomialFreimanRuzsaBinary`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted
