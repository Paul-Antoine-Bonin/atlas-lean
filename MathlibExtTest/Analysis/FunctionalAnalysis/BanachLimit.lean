/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.BanachLimit
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest

open Filter
open scoped BoundedContinuousFunction ContinuousLinearMap

/-- Obtain a Banach-limit witness from the proved existence theorem. -/
noncomputable def witness : (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  Classical.choose MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

private lemma witness_spec :
    (∀ f : ℕ →ᵇ ℝ, (∀ n, 0 ≤ f n) → 0 ≤ witness f) ∧
    witness (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 ∧
    (∀ f g : ℕ →ᵇ ℝ, (∀ n, g n = f (n + 1)) → witness f = witness g) ∧
    (∀ f : ℕ →ᵇ ℝ, ∀ l : ℝ,
      Tendsto (fun n => f n) atTop (nhds l) → witness f = l) :=
  Classical.choose_spec MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

/-- Positivity: the witness is nonnegative on pointwise-nonnegative sequences. -/
example (f : ℕ →ᵇ ℝ) (h : ∀ n, 0 ≤ f n) : 0 ≤ witness f :=
  witness_spec.1 f h

/-- Normalization: the witness sends the constant-one sequence to `1`. -/
example : witness (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 :=
  witness_spec.2.1

/-- Shift invariance: the witness agrees on a sequence and its left shift. -/
example (f g : ℕ →ᵇ ℝ) (h : ∀ n, g n = f (n + 1)) : witness f = witness g :=
  witness_spec.2.2.1 f g h

/-- Convergence extension: the witness returns the ordinary limit. -/
example (f : ℕ →ᵇ ℝ) (l : ℝ) (h : Tendsto (fun n => f n) atTop (nhds l)) :
    witness f = l :=
  witness_spec.2.2.2 f l h

/-- The witness evaluates every constant sequence at its value. -/
example (c : ℝ) : witness (BoundedContinuousFunction.const ℕ c) = c :=
  witness_spec.2.2.2 _ _ tendsto_const_nhds

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest
