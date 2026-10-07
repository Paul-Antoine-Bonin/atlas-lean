/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NStepLucasSequence

namespace MetaMathlibExt

example : nStepLucas 2 0 = 0 := by decide
example : nStepLucas 2 1 = 1 := by decide
example : nStepLucas 2 2 = 3 := by decide
example : nStepLucas 2 3 = 4 := by decide
example : nStepLucas 2 4 = 7 := by decide

end MetaMathlibExt
