/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PerrinSequence

namespace MetaMathlibExt

example : perrinSequence 0 = 3 := rfl
example : perrinSequence 1 = 0 := rfl
example : perrinSequence 2 = 2 := rfl
example : perrinSequence 3 = 3 := rfl
example : perrinSequence 4 = 2 := rfl
example : perrinSequence 5 = 5 := rfl

end MetaMathlibExt
