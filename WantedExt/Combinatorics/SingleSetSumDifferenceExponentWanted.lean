/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Single-set sum-difference exponent

The constant `C₃d` is the least real exponent that bounds the normalized
sumset cardinality by the corresponding normalized difference-set cardinality.
The frozen source states that its exact value is `2`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted

open scoped Pointwise

/-! Source record `C3d`, file SHA-256
`115fbd7c1cb17caa8e865a1dd2850589c09e102659247ffece53ad3824ec01cb`. -/

/-- A real exponent is admissible when it bounds the doubling constant by the corresponding
difference constant raised to that exponent for every nonempty finite integer set. -/
def IsAdmissibleExponent (θ : ℝ) : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    ((A + A).card : ℝ) / (A.card : ℝ) ≤
      Real.rpow (((A - A).card : ℝ) / (A.card : ℝ)) θ

/-- The single-set sum-difference exponent `C₃d`, using the source's equivalent
least-admissible-exponent formulation over finite integer sets. -/
noncomputable def singleSetSumDifferenceExponent : ℝ :=
  sInf {θ : ℝ | IsAdmissibleExponent θ}

/-- The resolved exact value `C₃d = 2` stated in the frozen source. -/
def singleSetSumDifferenceExponent_eq_two : Prop :=
  singleSetSumDifferenceExponent = 2

/--
Resolved true: The frozen optimization-problems source states that the problem is solved by Lin
and Li and that the single-set sum-difference exponent C3d equals 2; the known constructions
approach but do not attain the value. Source: Haowei Lin and Shanda Li, Settling the optimal
exponent relating sumsets and difference sets, arXiv:2607.27199v1 (2026),
https://arxiv.org/abs/2607.27199v1. Moved from
`OpenConjectures/Combinatorics/SingleSetSumDifferenceExponent`.
-/
public theorem_wanted singleSetSumDifferenceExponent_eq_two_holds : singleSetSumDifferenceExponent_eq_two

end MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted
