/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.NormalNumberSequence

namespace MetaMathlibExt

example (a : ℤ) : normalSeqFib a 3 = a ^ 2 + 1 := by
  simp [normalSeqFib, normalSeq]
  ring

example (a : ℤ) :
    normalSeqFib a 5 = normalSeqFib a 3 ^ 2 + normalSeqFib a 2 ^ 2 := by
  simpa using normalSeq_odd_identity a 3 (by omega)

end MetaMathlibExt
