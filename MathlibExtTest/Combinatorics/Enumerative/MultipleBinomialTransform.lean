/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MultipleBinomialTransform

example (a : ℕ → ℤ) (n : ℕ) :
    MetaMathlibExt.multipleBinomialTransform 0 a n = a n :=
  rfl

example (a : ℕ → ℤ) (n : ℕ) :
    MetaMathlibExt.multipleBinomialTransform 1 a n =
      MetaMathlibExt.binomialTransform a n :=
  rfl

example :
    MetaMathlibExt.multipleBinomialTransform 2 (fun n => (n : ℤ)) 2 = 6 := by
  decide
