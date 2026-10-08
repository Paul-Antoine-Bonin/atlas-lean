/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.Combinatorics.Enumerative.PQSuperPatalanNumbers

namespace MetaMathlibExt

private def binaryPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by omega
  hq_pos := by omega
  hq := by omega

example : pqSuperPatalanNumber binaryPatalanParams 0 0 = 1 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

example : pqSuperPatalanNumber binaryPatalanParams 1 0 = 2 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

end MetaMathlibExt
