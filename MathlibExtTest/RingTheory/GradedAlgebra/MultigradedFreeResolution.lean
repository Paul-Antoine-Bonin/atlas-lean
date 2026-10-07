/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedFreeResolution

@[expose] public section

-- The identity linear map preserves each homogeneous piece.
example {K : Type*} [Field K] {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (g : MetaMathlibExt.MultigradedPolynomialModule K n M) :
    MetaMathlibExt.IsDegreeZero g g LinearMap.id := fun _ _ hm => hm
