/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.NormOneIdeleClassGroup

@[expose] public section

noncomputable section

open NumberField

variable (K : Type*) [Field K] [NumberField K]

example : CommGroup (TopologicalIdeleGroup.NormOneIdeleClassGroup K) := inferInstance

example : IsTopologicalGroup (TopologicalIdeleGroup.NormOneIdeleClassGroup K) :=
  inferInstance

example (x : Kˣ) :
    QuotientGroup.mk (s := TopologicalIdeleGroup.normOnePrincipalIdeles K)
        ⟨TopologicalIdeleGroup.principalEmbedding (NumberField.RingOfIntegers K) K x,
          TopologicalIdeleGroup.principalIdeles_le_normOneIdeles K ⟨x, rfl⟩⟩ = 1 :=
  TopologicalIdeleGroup.normOne_mk_principalEmbedding K x

example :
    QuotientGroup.mk (s := TopologicalIdeleGroup.normOnePrincipalIdeles ℚ)
        ⟨TopologicalIdeleGroup.principalEmbedding (NumberField.RingOfIntegers ℚ) ℚ 1,
          TopologicalIdeleGroup.principalIdeles_le_normOneIdeles ℚ ⟨1, rfl⟩⟩ = 1 :=
  TopologicalIdeleGroup.normOne_mk_principalEmbedding ℚ 1
