/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.MathieuFibonacciFourierCoefficient

namespace MetaMathlibExt

example (n : {n : ℕ // 1 ≤ n}) :
    mathieuFibonacciFourierCoefficient n =
      (2 / Real.log ((1 + Real.sqrt 5) / 2)) *
        ‖Complex.Gamma (1 + 2 * (n.val : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Real.log ((1 + Real.sqrt 5) / 2) : ℂ))‖ ^ 2 :=
  rfl

end MetaMathlibExt
