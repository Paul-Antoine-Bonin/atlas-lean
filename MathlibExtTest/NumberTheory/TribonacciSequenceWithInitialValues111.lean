/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues111

@[expose] public section

namespace MetaMathlibExt

example : tribonacciWithInitialValues111 0 = 1 := rfl
example : tribonacciWithInitialValues111 1 = 1 := rfl
example : tribonacciWithInitialValues111 2 = 1 := rfl
example : tribonacciWithInitialValues111 3 = 3 := rfl
example : tribonacciWithInitialValues111 4 = 5 := rfl
example : tribonacciWithInitialValues111 5 = 9 := rfl

example (n : ℕ) :
    tribonacciWithInitialValues111 (n + 3) =
      tribonacciWithInitialValues111 (n + 2) +
        tribonacciWithInitialValues111 (n + 1) + tribonacciWithInitialValues111 n := rfl

#print axioms MetaMathlibExt.tribonacciWithInitialValues111

end MetaMathlibExt

end
