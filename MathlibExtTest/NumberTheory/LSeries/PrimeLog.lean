/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.PrimeLog

@[expose] public section

namespace PrimeLogTest

open scoped LSeries.notation

/-- The prime series, correction, and continuation elaborate as functions. -/
noncomputable example : ℂ → ℂ := Nat.Primes.logDirichletSeries

noncomputable example : ℂ → ℂ := Nat.Primes.logDirichletCorrection

noncomputable example : ℂ → ℂ := Nat.Primes.logDirichletContinuation

/-- One correction summand at the prime `2`, exponent offset `0`. -/
noncomputable example (s : ℂ) : ℂ :=
  Nat.Primes.logDirichletCorrectionTerm ⟨2, Nat.prime_two⟩ 0 s

/-- The correction series is analytic on `Re s > 1 / 2`. -/
example : AnalyticOnNhd ℂ Nat.Primes.logDirichletCorrection {s | 1 / 2 < s.re} :=
  Nat.Primes.logDirichletCorrection_analyticOn

/-- Von Mangoldt splitting at an arbitrary point with `Re s > 1`. -/
example (s : ℂ) (hs : 1 < s.re) :
    LSeries ↗ArithmeticFunction.vonMangoldt s
      = Nat.Primes.logDirichletSeries s + Nat.Primes.logDirichletCorrection s :=
  Nat.Primes.logDirichlet_vonMangoldt_split hs

/-- Logarithmic-derivative identity at an arbitrary point with `Re s > 1`. -/
example (s : ℂ) (hs : 1 < s.re) :
    Nat.Primes.logDirichletSeries s
      = -deriv riemannZeta s / riemannZeta s - Nat.Primes.logDirichletCorrection s :=
  Nat.Primes.logDirichletSeries_eq hs

/-- Destructuring the combined endpoint uses all three projections at once. -/
example : ∃ g : ℂ → ℂ, MeromorphicAt g ((((3 / 4 : ℝ))) : ℂ) ∧ AnalyticAt ℂ g 1 ∧
    g 2 = Nat.Primes.logDirichletSeries 2 - 1 / ((2 : ℂ) - 1) := by
  obtain ⟨g, hmero, hanal, hagree⟩ := Nat.Primes.logDirichlet_meromorphicContinuation
  have h34 : ((((3 / 4 : ℝ))) : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    change (1 / 2 : ℝ) < _
    rw [Complex.ofReal_re]
    norm_num
  have h1 : (1 : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by
    change (1 : ℝ) ≤ _
    rw [Complex.one_re]
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    change (1 : ℝ) < _
    norm_num
  exact ⟨g, hmero _ h34, hanal _ h1, hagree h2⟩

/-- Boundary analyticity of the canonical continuation at `s = 1`. -/
example : AnalyticAt ℂ Nat.Primes.logDirichletContinuation 1 :=
  Nat.Primes.logDirichletContinuation_analyticOn 1 (by
    change (1 : ℝ) ≤ _
    rw [Complex.one_re])

/-- Concrete agreement of the canonical continuation at `s = 2`. -/
example : Nat.Primes.logDirichletContinuation 2
    = Nat.Primes.logDirichletSeries 2 - 1 / ((2 : ℂ) - 1) :=
  Nat.Primes.logDirichletContinuation_agree (by
    change (1 : ℝ) < _
    norm_num)

/-- Meromorphic sample of the canonical continuation at real part `3 / 4`. -/
example : MeromorphicAt Nat.Primes.logDirichletContinuation ((((3 / 4 : ℝ))) : ℂ) :=
  Nat.Primes.logDirichletContinuation_meromorphic _ (by
    change (1 / 2 : ℝ) < _
    rw [Complex.ofReal_re]
    norm_num)

/-- Shifted continuation `s ↦ g (s + 1)`: smoke test for the N323 interface. -/
noncomputable def shiftedLogDirichletContinuation (s : ℂ) : ℂ :=
  Nat.Primes.logDirichletContinuation (s + 1)

/-- The shifted continuation is analytic on `Re s ≥ 0`. -/
example : AnalyticOnNhd ℂ shiftedLogDirichletContinuation {s | 0 ≤ s.re} := by
  have hf : AnalyticOnNhd ℂ (fun s : ℂ => s + 1) {s : ℂ | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hmaps : Set.MapsTo (fun s : ℂ => s + 1) {s : ℂ | 0 ≤ s.re} {s : ℂ | 1 ≤ s.re} := by
    intro x hx
    change (1 : ℝ) ≤ _
    have hx' : (0 : ℝ) ≤ x.re := hx
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hcomp := Nat.Primes.logDirichletContinuation_analyticOn.comp hf hmaps
  exact hcomp

end PrimeLogTest
