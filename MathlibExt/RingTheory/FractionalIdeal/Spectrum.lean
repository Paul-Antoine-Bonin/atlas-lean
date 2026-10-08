/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FractionalIdeal.GroupAction
public import MathlibExt.RingTheory.Spectrum.Prime.GroupAction

/-!
# Compatibility of fractional-ideal and prime-spectrum actions
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise

namespace PrimeSpectrum

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing K]
  [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]

/-- The prime-spectrum action is the restriction of the fractional-ideal action. -/
@[simp]
theorem smul_asIdeal_coe (g : G) (p : PrimeSpectrum R) :
    FractionalIdeal.coeIdeal (S := R⁰) (P := K) (g • p).asIdeal =
      g • FractionalIdeal.coeIdeal (S := R⁰) (P := K) p.asIdeal := by
  rw [smul_asIdeal, FractionalIdeal.smul_coeIdeal]

end PrimeSpectrum
