/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.FunctionField
public import MathlibExt.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

open IsDedekindDomain

namespace MathlibExtTest.RingTheory.DedekindDomain.AdicValuation

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

example (v : HeightOneSpectrum R) :
    (v.valuationSubringAtPrime K).toSubring =
      (v.adicCompletionIntegers K).toSubring.comap (algebraMap K (v.adicCompletion K)) :=
  v.valuationSubringAtPrime_eq_comap_adicCompletionIntegers

variable {F L : Type*} [Field F] [Field L] [Algebra (Polynomial F) L]
  [Algebra (RatFunc F) L] [IsScalarTower (Polynomial F) (RatFunc F) L]
  [FunctionField F L] [Algebra.IsSeparable (RatFunc F) L]

example (v : HeightOneSpectrum (FunctionField.ringOfIntegers F L)) :
    (v.valuationSubringAtPrime L).toSubring =
      (v.adicCompletionIntegers L).toSubring.comap (algebraMap L (v.adicCompletion L)) :=
  v.valuationSubringAtPrime_eq_comap_adicCompletionIntegers

end MathlibExtTest.RingTheory.DedekindDomain.AdicValuation
