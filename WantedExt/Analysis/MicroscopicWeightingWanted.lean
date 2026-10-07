/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Microscopic weightings of metric spaces
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.Analysis.MicroscopicWeightingWanted

open Filter Matrix

noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X]
    (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] :
    Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X]
    (t : ℝ) : X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X]
    [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Filter.Tendsto (weighting X) (nhdsWithin 0 (Set.Ioi 0)) (nhds w)

def IsGauging (X : Type*) [Fintype X] (M : Matrix X X ℝ) (g : X → ℝ)
    (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

def HasFiniteConcentration (X : Type*) [Fintype X] (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging X M g c

def microscopicWeightingIff : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X],
    HasMicroscopicWeighting X ↔ HasFiniteConcentration X (distanceMatrix X)

/--
Resolved false: Resolved false: Kenta Kitamura (assisted by ChatGPT) gave an explicit 10-point
metric space with finite concentration but no microscopic weighting, with a formal Lean proof.
Source: Kenta Kitamura, microscopic-weighting-counterexample, Lean formalization of the 10-point
counterexample,
https://github.com/KitaKen1/microscopic-weighting-counterexample/blob/eff8979/lean/MicroscopicWeightingCounterexampleFC.lean#L886-L894.
Moved from `OpenConjectures/Analysis/MicroscopicWeighting`.
-/
public theorem_wanted microscopicWeightingIff_refuted : ¬ microscopicWeightingIff

end MathlibExt.Analysis.MicroscopicWeightingWanted
