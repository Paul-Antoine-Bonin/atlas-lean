/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.Hankel

namespace Matrix

example {α : Type*} (s : ℕ → α) : hankel s 2 3 = s 5 := by
  rfl

example {α : Type*} (s : ℕ → α) : (hankel s)ᵀ = hankel s := by
  ext i j
  simp [add_comm]

example {α : Type*} (s : ℕ → α) :
    hankelFin 4 s (1 : Fin 4) (2 : Fin 4) = s 3 := by
  rfl

#print axioms hankel
#print axioms hankelFin

end Matrix
