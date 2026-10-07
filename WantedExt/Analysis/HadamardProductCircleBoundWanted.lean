/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hadamard product circle bound
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.HadamardProductCircleBoundWanted

/-! Source record `AMR-022-6028__2306028`. -/

/-- Normalized univalent class `S` with Taylor coefficients, cf. [AMR-022-6028] Problem 6.28. -/
structure ClassS where
  f : ℂ → ℂ
  a : ℕ → ℂ
  holo : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)
  map_zero : f 0 = 0
  deriv_one : HasDerivAt f 1 0
  inj : Set.InjOn f (Metric.ball (0 : ℂ) 1)
  coeff_zero : a 0 = 0
  coeff_one : a 1 = 1
  taylor : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun m => a m * z ^ m) (f z)

/-- Hadamard (coefficient-wise) product `P ∗ f`, cf. [AMR-022-6028] Problem 6.28. -/
noncomputable def hadamardProduct (a : ℕ → ℂ) (P : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (a k * P.coeff k) * (Polynomial.X : Polynomial ℂ) ^ k

/-- Supremum of `‖Q‖` over the unit circle `|z| = 1`, cf. [AMR-022-6028] Problem 6.28. -/
noncomputable def circleMax (Q : Polynomial ℂ) : ℝ :=
  sSup ((fun z => ‖Q.eval z‖) '' Metric.sphere (0 : ℂ) 1)

/-- Open question of [AMR-022-6028] Problem 6.28: does the Hadamard bound hold for all `S`, `n`,
`P`. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (S : ClassS) (P : Polynomial ℂ),
    P.natDegree ≤ n →
      circleMax (hadamardProduct S.a P n) ≤ (n : ℝ) * circleMax P

/--
Resolved true: Robertson's conjecture implies the bound (Sheil-Small, J. Reine Angew. Math. 258
(1973)), and de Branges (Acta Math. 154 (1985)) proved Milin's conjecture, hence Robertson's.
Both facts are recorded in Hayman-Lingham (arXiv:1809.07200, Problem 6.28, Update 6.1). Source:
Walter K. Hayman and Eleanor F. Lingham, Research Problems in Function Theory (New Edition),
arXiv:1809.07200v2 (2018), https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/HadamardProductCircleBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HadamardProductCircleBoundWanted
