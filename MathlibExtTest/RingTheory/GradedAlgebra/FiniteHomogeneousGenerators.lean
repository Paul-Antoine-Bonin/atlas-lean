/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.FiniteHomogeneousGenerators

@[expose] public section

open MetaMathlibExt

#check @MetaMathlibExt.MultigradedPolynomialModule.exists_finset_homogeneous_generators

public example (K : Type*) [Field K] (n : ℕ) (M : Type*)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MetaMathlibExt.MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ∃ s : Finset M,
      (∀ m ∈ s, ∃ α : Fin n →₀ Int, m ∈ targetGraded.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set M) = ⊤ :=
  MetaMathlibExt.MultigradedPolynomialModule.exists_finset_homogeneous_generators K n M targetGraded
