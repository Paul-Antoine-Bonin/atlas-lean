/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ModifiedBesselFirstKind
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example (x : ℝ) : modifiedBesselI_zero x = modifiedBesselI 0 x := rfl
example (x : ℝ) : modifiedBesselI_term 0 0 x = 1 := by
  norm_num [modifiedBesselI_term]
example (x : ℝ) : modifiedBesselI_term 1 0 x = x / 2 := by
  norm_num [modifiedBesselI_term]

end MetaMathlibExt
