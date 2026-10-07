/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- Ramanujan's master theorem (statement id `ramanujan-master-s1`).

Source: https://en.wikipedia.org/wiki/Ramanujan%27s_master_theorem
(Raw: `int_0^infty x^{s-1} sum_k phi(k)(-x)^k/k! dx = Gamma(s) phi(-s)`.)

This specialization assumes `0 < a < b`, `a < re(s) < b`, analyticity of `φ`
on the half-plane `re(z) > -b`, and a uniform vertical exponential bound with
rate strictly below `π`.  For positive real `x`, `F x` is normalized by the
exponential generating series `sum φ(k) * (-x)^k / k!`; the displayed
integrability hypothesis supplies convergence of its Lebesgue Mellin integral
over `(0, ∞)`.  Complex powers use Mathlib's principal-log normalization.  Under
these hypotheses the integral equals `Gamma(s) * φ(-s)`. -/
theorem_wanted Ramanujan_master_theorem
    (φ : ℂ → ℂ) (F : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (ha : 0 < a) (hab : a < b)
    (hs : a < s.re ∧ s.re < b)
    (hφ : AnalyticOn ℂ φ {z : ℂ | -b < z.re})
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∃ P : ℝ, P < Real.pi ∧
      ∀ u v : ℝ, -b < u → ‖φ (Complex.mk u v)‖ ≤ C * Real.exp (P * |v|))
    (hF : ∀ x : ℝ, 0 < x →
      HasSum (fun k : ℕ => φ (k : ℂ) * (-(x : ℂ)) ^ k / (k.factorial : ℂ)) (F x))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((x : ℂ) ^ (s - 1) * F x : ℂ))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume)
    : ∫ x in Set.Ioi (0 : ℝ), ((x : ℂ) ^ (s - 1) * F x) ∂MeasureTheory.volume
      = Complex.Gamma s * φ (-s)

end

end MetaMathlibExt
