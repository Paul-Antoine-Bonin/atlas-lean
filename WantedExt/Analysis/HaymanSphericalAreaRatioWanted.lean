/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-1016 (W. K. Hayman): for `f` meromorphic in the plane, with
`n(r) = sup_a` (number of roots of `f(z) = a` in `|z| < r`, counted with
multiplicity) and `A(r)` the normalized spherical-area integral, it is
known that `1 ≤ liminf_{r → ∞} n(r)/A(r) ≤ e`. Can `e` be replaced by
`1`, i.e. is `liminf_{r → ∞} n(r)/A(r) = 1`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.Analysis.HaymanSphericalAreaRatioWanted

/-! Source record `AMR-022-1016`. -/

/-- `rootCount f a r`: number of roots of `f(z) = a` in `|z| < r`,
counted with multiplicity, as the finite-support sum over `z : ℂ` of the
nonnegative part of the divisor of `f - a` on `Metric.ball 0 r`. -/
noncomputable def rootCount (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, (MeromorphicOn.divisor (fun z => f z - a) (Metric.ball 0 r) z).toNat

/-- `n f r`: supremum over `a` of `rootCount f a r`, as a real number.
This is a conditional real supremum, so it is only meaningful when the
range of root counts at radius `r` is bounded above; see
`HasBoundedRootCounts`. -/
noncomputable def n (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range (fun a : ℂ => (rootCount f a r : ℝ)))

/-- `sphericalDensity f z`: normalized spherical-area density
`‖f'(z)‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2`, with `f'(z) = deriv f z`. -/
noncomputable def sphericalDensity (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2

/-- `A f r`: normalized spherical area of `f` on the disk `|z| < r`,
i.e. `(1 / π)` times the Lebesgue integral of `sphericalDensity f`
over `Metric.ball 0 r`. -/
noncomputable def A (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ z in Metric.ball (0 : ℂ) r, sphericalDensity f z

/-- A function `f : ℂ → ℂ` is nonconstant in the germ-wise sense: there
are two points at which `f` is differentiable (analytic points of the
meromorphic germ) with different values. This excludes pointwise-modified
constant representatives (for example `f 0 = 1`, `f z = 0` elsewhere),
which are meromorphic with zero derivative density but represent the
constant-zero germ. -/
def IsNonconstant (f : ℂ → ℂ) : Prop :=
  ∃ u v : ℂ, DifferentiableAt ℂ f u ∧ DifferentiableAt ℂ f v ∧ f u ≠ f v

/-- `HasBoundedRootCounts f`: for every radius `r`, the real-valued root
counts `rootCount f a r` are bounded above as `a` varies, so that the
conditional supremum `n f r` is taken over a bounded set. -/
def HasBoundedRootCounts (f : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, BddAbove (Set.range (fun a : ℂ => (rootCount f a r : ℝ)))

/-- [AMR-022-1016] Hayman's question: is
`liminf_{r → ∞} n(r)/A(r) = 1` for every globally meromorphic,
nonconstant `f` with bounded root counts at each radius?
The known bounds `1 ≤ liminf n(r)/A(r) ≤ e` are not formalized here. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ → IsNonconstant f →
    HasBoundedRootCounts f ∧
      Filter.liminf (fun r : ℝ => n f r / A f r) Filter.atTop = 1

/--
Resolved false: Toppila constructed a nonconstant meromorphic function with liminf n(r)/A(r) >=
80/79, and Hinkkanen and Miles (arXiv:2401.13808, 2024, Theorem 1.1) give one with liminf
n(r)/A(r) >= 1.07328, so the universal claim liminf = 1 is false. Source: A. Hinkkanen and J.
Miles, Maximum and Average Valence of Meromorphic Functions, arXiv preprint (2024),
arXiv:2401.13808, https://arxiv.org/abs/2401.13808. Moved from
`OpenConjectures/Analysis/HaymanSphericalAreaRatio`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.HaymanSphericalAreaRatioWanted
