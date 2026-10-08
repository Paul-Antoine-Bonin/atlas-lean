/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedRascalTriangle

namespace MetaMathlibExt

example (c d d₁ d₂ : ℤ) :
    IsGeneralizedRascalTriangle fun r k =>
      c + (k : ℤ) * d₁ + (r : ℤ) * d₂ + (r : ℤ) * (k : ℤ) * d := by
  exact ⟨c, d, d₁, d₂, fun _ _ => rfl⟩

end MetaMathlibExt
