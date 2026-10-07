/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.FallingKBinomialTransform

namespace MetaMathlibExt

example : fallingKBinomialTransform 2 (fun n => n) 2 = 6 := by
  norm_num [fallingKBinomialTransform, Finset.sum_range_succ]

example : binomialTransform (fun n => n) 2 = 4 := by
  norm_num [binomialTransform, fallingKBinomialTransform, Finset.sum_range_succ]

end MetaMathlibExt
