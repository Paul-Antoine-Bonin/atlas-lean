/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductSurjective

@[expose] public section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K))

noncomputable section

example : DenseRange (fun y : L => fun w : v.placesOver L =>
    algebraMap L (w.val.adicCompletion L) y) :=
  denseRange_algebraMap_placesOver v

example : DenseRange (completionTensorProductMap (K := K) (L := L) v) :=
  denseRange_completionTensorProductMap v

example : Function.Surjective
    (completionTensorProductMap (K := K) (L := L) v) :=
  completionTensorProductMap_surjective v

example (t : (w : v.placesOver L) → w.val.adicCompletion L) :
    ∃ s, completionTensorProductMap (K := K) (L := L) v s = t :=
  completionTensorProductMap_surjective v t

end
