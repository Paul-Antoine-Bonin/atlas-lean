/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBaseChangedTermDecomposition

@[expose] public section

namespace MetaMathlibExt

universe u

public noncomputable example {K : Type u} [Field K] {n : ℕ} {M : Type u}
    [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u) (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) :
    DirectSum.Decomposition
      (fun α => baseChangedDegreePiece targetGraded resolution ι res i α) :=
  MultigradedFreeResolution.baseChangedDegreeDecomposition targetGraded resolution ι res i

#check @MetaMathlibExt.MultigradedFreeResolution.baseChangedDegreeDecomposition

end MetaMathlibExt
