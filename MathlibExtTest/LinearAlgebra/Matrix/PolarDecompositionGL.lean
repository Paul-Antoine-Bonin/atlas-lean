/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.Factorizations.Polar
import MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGL

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Uniqueness makes the polar decomposition of a positive-definite matrix `1 * A`.
example {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) (hA : A.PosDef) :
    ∃ (U : Matrix.unitaryGroup n 𝕜) (P : Matrix n n 𝕜),
      P.PosDef ∧ A = (U : Matrix n n 𝕜) * P ∧ U = 1 ∧ P = A := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  obtain ⟨U, P, hP, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det A hdet
  obtain ⟨hUone, hPA⟩ := huniq 1 A hA (by simp)
  exact ⟨U, P, hP, hdecomp, hUone.symm, hPA.symm⟩
