/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverRamificationIndex

/-!
# Test file
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

example : Function.Injective (adicCompletionIntegersMap v w) :=
  adicCompletionIntegersMap_injective v w

example :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
  ramificationIdx_adicCompletionIntegersMap v w

example :
    ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) = 1) ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [ramificationIdx_adicCompletionIntegersMap v w]

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
