/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverValuation

/-!
# Checks for the completion valuation formula
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

-- Valuation formula on a general completed point.
example (x : v.adicCompletion K) :
    Valued.v (adicCompletionMap v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal :=
  valuation_adicCompletionMap v w x

-- Integrality is preserved.
example (x : v.adicCompletion K) (hx : x ∈ v.adicCompletionIntegers K) :
    adicCompletionMap v w x ∈ w.adicCompletionIntegers L :=
  adicCompletionMap_mem_integers v w x hx

-- Restricted map agrees with the full map after coercion.
example (x : v.adicCompletionIntegers K) :
    ((adicCompletionIntegersMap v w x : w.adicCompletionIntegers L) :
      w.adicCompletion L) = adicCompletionMap v w (x : v.adicCompletion K) :=
  adicCompletionIntegersMap_apply v w x

-- Algebra-map inputs are fixed by the completion map.
example (k : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) k) =
      algebraMap K (w.adicCompletion L) k :=
  adicCompletionMap_algebraMap v w k

end IsDedekindDomain.HeightOneSpectrum
