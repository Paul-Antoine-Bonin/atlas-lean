/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DiagonalSumsOfARiordanOrTriangularArray

namespace MetaMathlibExt

example {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ → M) (n : ℕ) :
    diagonalSums a n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 ij.2 :=
  rfl

#print axioms diagonalSums

end MetaMathlibExt
