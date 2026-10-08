/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication

@[expose] public section

namespace PeriodPair

variable (L : PeriodPair)

example : (0 : ℂ) ∈ L.endomorphismRing := by
  simp

example : (1 : ℂ) ∈ L.endomorphismRing := by
  simp

example : L.IsProperIdeal L.endomorphismRing := by
  simp

end PeriodPair
