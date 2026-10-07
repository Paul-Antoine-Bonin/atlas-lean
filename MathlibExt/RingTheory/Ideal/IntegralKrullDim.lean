/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-- Krull dimension cannot increase along an integral extension of commutative rings.

This is the dimension consequence of strict contraction of prime ideals
(`Ideal.IsIntegral.comap_lt_comap`): contraction gives a strictly monotone map
`PrimeSpectrum B → PrimeSpectrum A`, hence the inequality of Krull dimensions. -/
theorem ringKrullDim_le_of_integral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
    (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)
