/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FermatPrime
public import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExt

example : IsFermatPrime 3 := by
  refine ⟨by norm_num, 0, ?_⟩
  rfl

example : IsFermatPrime 5 := by
  refine ⟨by norm_num, 1, ?_⟩
  rfl

end MetaMathlibExt
