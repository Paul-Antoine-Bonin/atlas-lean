/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Lie.LeviDecomposition

import Mathlib.Algebra.Lie.Semisimple.Basic

@[expose] public section

namespace MathlibExtTest.Algebra.Lie.LeviDecomposition

-- For a semisimple algebra, the Levi factor supplied by the theorem spans the whole algebra.
example {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      (S : Submodule K L) = ⊤ := by
  obtain ⟨S, hS, hsum, _⟩ :=
    MathlibExt.Algebra.Lie.LandmarkWanted.levi_decomposition (K := K) (L := L)
  exact ⟨S, hS, by simpa using hsum⟩

-- Weyl's theorem gives every ideal of a semisimple algebra an invariant complement.
example {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    ∃ J : LieIdeal K L, IsCompl I J := by
  exact LieModule.exists_isCompl_of_isSemisimple I

end MathlibExtTest.Algebra.Lie.LeviDecomposition
