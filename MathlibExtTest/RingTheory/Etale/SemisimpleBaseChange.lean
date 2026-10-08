/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.SemisimpleBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

open scoped TensorProduct

variable {K Ω B : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
  [CommRing B] [Algebra K B] [Module.Finite K B]

-- Generalized theorem over an arbitrary algebraically closed extension.
example (h : IsSemisimpleRing (Ω ⊗[K] B)) : Algebra.Etale K B :=
  Algebra.Etale.of_isSemisimpleRing_tensorProduct h

-- ATLAS input orientation, transported across `comm` to the new theorem.
example (h : IsSemisimpleRing (B ⊗[K] AlgebraicClosure K)) :
    Algebra.Etale K B := by
  have : IsSemisimpleRing (B ⊗[K] AlgebraicClosure K) := h
  have : IsSemisimpleRing (AlgebraicClosure K ⊗[K] B) :=
    (Algebra.TensorProduct.comm K B (AlgebraicClosure K)).toRingEquiv.isSemisimpleRing
  exact Algebra.Etale.of_isSemisimpleRing_tensorProduct
    (Ω := AlgebraicClosure K) inferInstance
