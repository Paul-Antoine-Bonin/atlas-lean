/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

namespace MetaMathlibExt

example : ordinaryRiordanPascalLikeMatrix 0 0 0 = 1 := by decide
example : ordinaryRiordanPascalLikeMatrix 2 1 1 = 3 := by decide
example : ordinaryRiordanPascalLikeMatrix 3 1 1 = 5 := by decide

end MetaMathlibExt
