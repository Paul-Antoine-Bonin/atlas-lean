/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PadovanSequence

@[expose] public section

namespace MetaMathlibExt

example : shiftedPadovanSequence 0 = 1 := rfl
example : shiftedPadovanSequence 1 = 0 := rfl
example : shiftedPadovanSequence 2 = 1 := rfl
example : shiftedPadovanSequence 3 = 1 := rfl
example : shiftedPadovanSequence 4 = 1 := rfl
example : shiftedPadovanSequence 5 = 2 := rfl

example (n : Nat) :
    shiftedPadovanSequence (n + 3) =
      shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n := rfl

#print axioms MetaMathlibExt.shiftedPadovanSequence
#print axioms MetaMathlibExt.shiftedPadovanSequence_zero
#print axioms MetaMathlibExt.shiftedPadovanSequence_one
#print axioms MetaMathlibExt.shiftedPadovanSequence_two
#print axioms MetaMathlibExt.shiftedPadovanSequence_add_three

end MetaMathlibExt

end
