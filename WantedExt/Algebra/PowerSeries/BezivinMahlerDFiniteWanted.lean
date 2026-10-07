/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section

namespace MetaMathlibExt

/-! # Bezivin theorem: D-finite Mahler functions are rational
-/

/--
A `k`-Mahler power series over `ℂ` that is D-finite is a rational function.

Source: Jason P. Bell, Michael Coons, and Eric Rowland,
"The Rational-Transcendental Dichotomy of Mahler Functions,"
Journal of Integer Sequences 16 (2013), Article 13.2.10,
Theorem [Bézivin] (label Df), lines 163–164,
https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex

The `k`-Mahler functional equation is the source's equation (label F),
line 155; D-finiteness (homogeneous linear differential equation with
polynomial coefficients) is recalled on line 161. The Mahler side sums
`(p i) * F(X ^ k ^ i)` via power-series substitution; the D-finite side
sums `(q j) * F^{(j)}` via iterated derivatives; rationality is
`F * Q = P` for polynomials with `Q ≠ 0`.
-/
public theorem_wanted bezivin_mahler_dfinite_rational
    (k : ℕ) (hk : 2 ≤ k) (F : PowerSeries ℂ) :
    (∃ d : ℕ, ∃ p : Fin (d + 1) → Polynomial ℂ, (∃ i, p i ≠ 0) ∧
      ∑ i, (p i).toPowerSeries *
        PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ k ^ i.val) F = 0) →
    (∃ d : ℕ, ∃ q : Fin (d + 1) → Polynomial ℂ, (∃ j, q j ≠ 0) ∧
      ∑ j, (q j).toPowerSeries * (⇑(PowerSeries.derivative))^[j.val] F = 0) →
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ F * Q.toPowerSeries = P.toPowerSeries

end MetaMathlibExt
