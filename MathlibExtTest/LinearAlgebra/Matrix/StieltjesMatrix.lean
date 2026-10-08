/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.StieltjesMatrix

namespace MetaMathlibExt

example {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) :
    stieltjesMatrix a1 b1 a b 0 0 = a1 := by
  simp [stieltjesMatrix]

example {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) :
    stieltjesMatrix a1 b1 a b 2 1 = b := by
  simp [stieltjesMatrix]

example {R : Type*} [AddMonoidWithOne R] (a b lam mu : R) :
    stieltjesMatrixOf a b lam mu 0 0 = a + lam := by
  simp [stieltjesMatrixOf, stieltjesMatrix]

end MetaMathlibExt
