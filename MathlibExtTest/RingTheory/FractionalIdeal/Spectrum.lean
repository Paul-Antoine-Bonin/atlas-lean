/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FractionalIdeal.Spectrum

/-!
# Tests for compatibility of fractional-ideal and prime-spectrum actions
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise

namespace N150Test

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] (g : G) (p : PrimeSpectrum R) :
    FractionalIdeal.coeIdeal (S := R⁰) (P := K) (g • p).asIdeal =
      g • FractionalIdeal.coeIdeal (S := R⁰) (P := K) p.asIdeal :=
  PrimeSpectrum.smul_asIdeal_coe g p

end N150Test
