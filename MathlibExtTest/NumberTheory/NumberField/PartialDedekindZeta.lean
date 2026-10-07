/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.PartialDedekindZeta

@[expose] public section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

example (s : ℂ) : partialDedekindZeta K ∅ s = 1 := by
  simp

example (𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)) (s : ℂ) :
    partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp

end NumberField
