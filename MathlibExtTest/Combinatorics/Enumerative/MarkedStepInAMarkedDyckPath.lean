/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath

namespace MetaMathlibExt

open MarkedDyckStep

example : markedDyckCountE [E, Nstar, E, N] = 2 := by rfl
example : markedDyckCountN [E, Nstar, E, N] = 1 := by rfl
example : markedDyckCountNstar [E, Nstar, E, N] = 1 := by rfl

end MetaMathlibExt
