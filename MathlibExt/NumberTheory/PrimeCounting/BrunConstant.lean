/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

/-!
# Brun's constant

Brun's constant is the sum of the reciprocals of the primes in every twin-prime pair.
-/

/-- The reciprocal contribution of the twin-prime pair whose smaller member is `p`.

Source: teorth/optimizationproblems, “Brun's Constant,” `constants/81a.md`; the convention counts a
prime once for every twin-prime pair containing it.
-/
noncomputable def brunTwinPrimeReciprocalTerm (p : ℕ) : ℝ :=
  if p.Prime ∧ (p + 2).Prime then
    (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
  else 0

@[simp]
theorem brunTwinPrimeReciprocalTerm_eq_zero (p : ℕ)
    (h : ¬(p.Prime ∧ (p + 2).Prime)) :
    brunTwinPrimeReciprocalTerm p = 0 := by
  simp [brunTwinPrimeReciprocalTerm, h]

theorem brunTwinPrimeReciprocalTerm_eq (p : ℕ)
    (h : p.Prime ∧ (p + 2).Prime) :
    brunTwinPrimeReciprocalTerm p =
      (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ) := by
  simp [brunTwinPrimeReciprocalTerm, h]

/-- The twin-prime reciprocal terms are summable. -/
theorem summable_brunTwinPrimeReciprocalTerm :
    Summable brunTwinPrimeReciprocalTerm := by
  exact BrunTwinPrimeReciprocalsWanted.brun_twin_prime_reciprocal_series_summable

/-- Brun's constant, with a shared prime such as `5` counted once for each twin-prime pair. -/
noncomputable def brunConstant : ℝ :=
  ∑' p : ℕ, brunTwinPrimeReciprocalTerm p

/-- The defining twin-prime reciprocal series has Brun's constant as its sum. -/
theorem hasSum_brunConstant :
    HasSum brunTwinPrimeReciprocalTerm brunConstant :=
  summable_brunTwinPrimeReciprocalTerm.hasSum

end MathlibExt.NumberTheory.PrimeCounting
