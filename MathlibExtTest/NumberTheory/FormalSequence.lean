/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FormalSequence
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : IsFormalSequence (fun _ => (1 : ℚ)) 1 1 1 := by
  norm_num [IsFormalSequence, formalAlpha, formalBeta]

example : ¬ IsFormalSequence (fun _ => (0 : ℚ)) 0 0 0 := by
  simp [IsFormalSequence]

example : ¬ IsFormalSequence (fun n => (n : ℚ)) 0 1 2 := by
  intro h
  have hrec := h.2.2.2.2 1
  norm_num [formalAlpha, formalBeta] at hrec

end MetaMathlibExt
