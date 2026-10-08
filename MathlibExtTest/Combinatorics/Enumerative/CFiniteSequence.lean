/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CFiniteSequence

namespace MetaMathlibExt

example : IsCFiniteSequence (fun _ : ℕ => (1 : MvPolynomial Unit ℤ)) := by
  refine ⟨1, 0, fun _ => 1, ?_⟩
  intro n hn
  simp

end MetaMathlibExt
