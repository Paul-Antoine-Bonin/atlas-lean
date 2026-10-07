/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherOrderHarmonic

#check @higherHarmonic
#check @higherHarmonic_zero
#check @higherHarmonic_succ
#check @higherHarmonic_one
#check @higherHarmonic_order_one

example : higherHarmonic 0 2 = 0 :=
  higherHarmonic_zero 2

example : higherHarmonic 1 2 = 1 :=
  higherHarmonic_one 2

example : higherHarmonic (1 + 1) 2 =
    higherHarmonic 1 2 + (1 : Rat) / ((((1 + 1 : Nat)) : Rat) ^ 2) :=
  higherHarmonic_succ 1 2

example : higherHarmonic 2 1 = harmonic 2 :=
  higherHarmonic_order_one 2
