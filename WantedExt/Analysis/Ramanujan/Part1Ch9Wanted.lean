/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9 — wishlist

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), recorded as `theorem_wanted` declarations.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9


namespace Entry27Clausen

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9FallingDerivative (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ range (m + 1),
    ∏ q ∈ (range (m + 1)).erase j, (r - q)

def chapter9Entry27Coeff (k : ℕ) (r : ℝ) : ℝ :=
  (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
    chapter9FallingDerivative (2 * k - 2) r

def chapter9Entry27Approx (r C : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  C - Real.rpow x (r + 1) / (r + 1) ^ 2 +
    ∑ j ∈ range N,
      let k := j + 1
      chapter9Entry27Coeff k r * Real.rpow x (r - 2 * (k : ℝ) + 1)

def chapter9Entry27LogTerm (r : ℝ) (j : ℕ) : ℝ :=
  Real.log (j + 1 : ℝ) / Real.rpow (j + 1 : ℝ) (r + 1)

def chapter9PhiR (r x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (Nat.floor x),
    Real.rpow (k : ℝ) r * Real.log k

def chapter9PowerSumR (r x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (Nat.floor x), Real.rpow (k : ℝ) r

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9. -/
theorem_wanted ramanujan_part1_ch9_entry27_clausen (r : ℝ) (hr : -1 < r) :
    ∃ C : ℝ,
      (∀ N : ℕ, Asymptotics.IsBigO
        (Filter.map (fun n : ℕ => (n : ℝ)) atTop)
        (fun x : ℝ =>
          chapter9PhiR r x - Real.log x *
              (chapter9PowerSumR r x - (riemannZeta (-r : ℂ)).re) -
            chapter9Entry27Approx r C N x)
        (fun x : ℝ => Real.rpow x (r - 2 * (N : ℝ) - 1))) ∧
      (0 < r →
        0 < Real.Gamma (r + 1) ∧
        Summable (chapter9Entry27LogTerm r) ∧
        C =
          2 * Real.Gamma (r + 1) * (riemannZeta (r + 1 : ℂ)).re /
              Real.rpow (2 * Real.pi) (r + 1) *
            (Real.sin (Real.pi * r / 2) *
                (Real.log (2 * Real.pi) -
                  deriv Real.Gamma (r + 1) / Real.Gamma (r + 1)) -
              Real.pi / 2 * Real.cos (Real.pi * r / 2)) +
          2 * Real.Gamma (r + 1) * Real.sin (Real.pi * r / 2) /
              Real.rpow (2 * Real.pi) (r + 1) *
            ∑' j : ℕ, chapter9Entry27LogTerm r j)

end

end Entry27Clausen

end MathlibExt.Analysis.Ramanujan.Part1Ch9
