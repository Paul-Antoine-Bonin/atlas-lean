/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted

/-!
Clause list for [AMR-022-8011] Problem 8.11:
(a) functions analytic in |z| < 1; (b) finite Dirichlet integral;
(c) g is in D; (d) Pg (as defined in Problem 8.10) is dense in D;
(e) f is in D; (f) |f(z)| >= |g(z)| for all |z| < 1;
question: is Pf necessarily dense in D.
Density is in the Dirichlet norm
`‖u‖² = |u 0|² + ∫_{|z|<1} |u'(z)|²`, stated explicitly below rather
than via a topology on the subtype of all functions `ℂ → ℂ` (whose
inherited product topology would be the wrong one, and would make
values outside the disc matter). Membership `h ∈ Pg` likewise only
constrains values on the disc.
Context-only evidence (analogues in H^2 and A^2, Shields g = 1 case,
status/rights/difficulty metadata) is not formalized.
-/

/-- Dirichlet space D from [AMR-022-8011] (Hayman, Research Problems in Function Theory (2018), Problem 8.11, https://arxiv.org/abs/1809.07200): functions analytic in |z| < 1 with finite Dirichlet integral. -/
abbrev DirichletSpace := { f : ℂ → ℂ // AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧ MeasureTheory.IntegrableOn (fun z => ‖deriv f z‖ ^ 2) (Metric.ball (0 : ℂ) 1) MeasureTheory.volume }

/-- Polynomial multiples Pg from [AMR-022-8011] Problem 8.11, Pg as defined in Problem 8.10 (Hayman (2018); https://arxiv.org/abs/1809.07200): products of the fixed function `g ∈ D` by analytic polynomials, with equality required on the disc only. -/
def polyTimes (g : DirichletSpace) : Set DirichletSpace :=
  { h | ∃ p : Polynomial ℂ, ∀ z : ℂ, ‖z‖ < 1 → h.val z = p.eval z * g.val z }

/-- Density in the Dirichlet norm: `S` is dense in `D` when every
`u ∈ D` is approximated arbitrarily well by elements of `S` in
`|u 0|² + ∫_{|z| < 1} |u'(z)|²`. -/
def IsDirichletDense (S : Set DirichletSpace) : Prop :=
  ∀ u : DirichletSpace, ∀ ε : ℝ, 0 < ε →
    ∃ h ∈ S, ‖h.val 0 - u.val 0‖ ^ 2 +
      (∫ z in Metric.ball (0 : ℂ) 1, ‖deriv h.val z - deriv u.val z‖ ^ 2
        ∂MeasureTheory.volume) < ε

/-- Open question from [AMR-022-8011] (Hayman (2018), Problem 8.11, https://arxiv.org/abs/1809.07200): if Pg is dense in D and |f| >= |g| on the disc, is Pf necessarily dense in D. -/
def conjecture : Prop :=
  ∀ (g f : DirichletSpace), IsDirichletDense (polyTimes g) → (∀ z : ℂ, ‖z‖ < 1 → ‖g.val z‖ ≤ ‖f.val z‖) → IsDirichletDense (polyTimes f)
/--
Resolved true: Richter and Sundberg (Michigan Math. J. 38 (1991) 355-379), and independently
Aleman, proved that in Dirichlet-type spaces D(mu), including the classical Dirichlet space, |g|
<= |f| with g cyclic implies f cyclic (restated in arXiv:2406.06182, Thm 5.12). Source: Emmanuel
Fricain and Romain Lebreton, Cyclicity of the shift operator through Bezout identities,
arXiv:2406.06182 (2024), https://arxiv.org/abs/2406.06182. Moved from
`OpenConjectures/Analysis/DirichletSpacePolynomialDensity`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted
