/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductEquiv

@[expose] public section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K))

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

example : Function.Injective
    (completionTensorProductMap (K := K) (L := L) v) :=
  completionTensorProductMap_injective v

-- N236/Theorem 11.23(5)'s coordinate formula, used by N265, with tensor factors swapped.
example (x : v.adicCompletion K) (y : L) (w : v.placesOver L) :
    completionTensorProductAlgEquiv (K := K) (L := L) v (x ⊗ₜ[K] y) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
  completionTensorProductAlgEquiv_tmul (K := K) (L := L) v x y w

example (z : (w : v.placesOver L) → w.val.adicCompletion L) :
    completionTensorProductAlgEquiv (K := K) (L := L) v
      ((completionTensorProductAlgEquiv (K := K) (L := L) v).symm z) = z :=
  AlgEquiv.apply_symm_apply _ z

example (y : L) (x : v.adicCompletion K) (w : v.placesOver L) :
    completionTensorProductRightAlgEquiv (K := K) (L := L) v
        (y ⊗ₜ[K] x) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
  completionTensorProductRightAlgEquiv_tmul (K := K) (L := L) v y x w

example (y : L) (w : v.placesOver L) :
    completionTensorProductRightAlgEquiv (K := K) (L := L) v
        (y ⊗ₜ[K] (1 : v.adicCompletion K)) w =
      algebraMap L (w.val.adicCompletion L) y :=
  completionTensorProductRightAlgEquiv_tmul_one (K := K) (L := L) v y w

example
    (z : (w : v.placesOver L) → w.val.adicCompletion L) :
    completionTensorProductRightAlgEquiv (K := K) (L := L) v
      ((completionTensorProductRightAlgEquiv (K := K) (L := L) v).symm
        z) = z :=
  AlgEquiv.apply_symm_apply _ z

example :
    Nonempty
      (L ⊗[K] v.adicCompletion K ≃ₐ[K]
        ((w : v.placesOver L) → w.val.adicCompletion L)) :=
  completionTensorProductRightAlgEquiv_K (K := K) (L := L) v

end
