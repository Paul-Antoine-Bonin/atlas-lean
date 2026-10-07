/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverMaximalIdeal

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example :
    Ideal.comap (adicCompletionIntegersMap v w)
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
  comap_maximalIdeal_adicCompletionIntegersMap v w

example (x : v.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    adicCompletionIntegersMap v w x ∈
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) := by
  have h := comap_maximalIdeal_adicCompletionIntegersMap v w
  rw [← h] at hx
  exact Ideal.mem_comap.mp hx

example (x : v.adicCompletionIntegers K)
    (hx : adicCompletionIntegersMap v w x ∈
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have h := comap_maximalIdeal_adicCompletionIntegersMap v w
  rw [← h]
  exact Ideal.mem_comap.mpr hx

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
