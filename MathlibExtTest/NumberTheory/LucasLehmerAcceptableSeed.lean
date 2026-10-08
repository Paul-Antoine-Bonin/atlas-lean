/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.LucasLehmerAcceptableSeed

open MetaMathlibExt

-- The Jacobi conditions for seed 4 certify the Mersenne prime 31.
example : Nat.Prime (mersenne 5) := by
  apply (acceptableSeed_of_jacobi 5 (by decide) (by norm_num) 4 (by
    norm_num [mersenne])).2
  norm_num [mersenne, Function.iterate_succ_apply']
