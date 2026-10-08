/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedPolynomialModule

@[expose] public section

-- The zero exponent embeds as the zero grading index.
example {n : ℕ} : MetaMathlibExt.natDegreeToInt (0 : Fin n →₀ ℕ) = 0 := by
  simp [MetaMathlibExt.natDegreeToInt]

-- Embedded exponents add: shifting by `a + b` is shifting by `a` then `b`.
example {n : ℕ} (a b : Fin n →₀ ℕ) :
    MetaMathlibExt.natDegreeToInt (a + b) =
      MetaMathlibExt.natDegreeToInt a + MetaMathlibExt.natDegreeToInt b := by
  unfold MetaMathlibExt.natDegreeToInt
  ext i
  simp
