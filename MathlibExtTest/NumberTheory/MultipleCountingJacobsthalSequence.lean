/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleCountingJacobsthalSequence

namespace MetaMathlibExt

example : multipleCountingJacobsthalSequence 2 3 0 = 0 := by decide
example : multipleCountingJacobsthalSequence 2 3 1 = 1 := by decide
example : multipleCountingJacobsthalSequence 3 5 2 = 4 := by decide

#print axioms multipleCountingJacobsthalSequence

end MetaMathlibExt
