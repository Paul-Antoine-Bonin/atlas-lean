/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellNumberSequence

@[expose] public section

namespace MetaMathlibExt

example : pellNumber 0 = 0 := rfl
example : pellNumber 1 = 1 := rfl
example : pellNumber 2 = 2 := rfl
example : pellNumber 3 = 5 := rfl
example : pellNumber 4 = 12 := rfl
example : pellNumber 5 = 29 := rfl

example (n : ℕ) :
    pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl

#print axioms MetaMathlibExt.pellNumber

end MetaMathlibExt

end
