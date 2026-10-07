/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

namespace MetaMathlibExt

example : IsCyclicNumber 15 := by
  unfold IsCyclicNumber
  decide

example : ¬ IsCyclicNumber 4 := by
  unfold IsCyclicNumber
  decide
example : oppermannCyclicCountLeft 2 = 2 := by decide

end MetaMathlibExt
