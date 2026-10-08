/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SCullenNumber

@[expose] public section

example : MetaMathlibExt.sCullenNumber 2 1 = 3 := rfl
example : MetaMathlibExt.sCullenNumber 2 2 = 9 := rfl
example : MetaMathlibExt.sCullenNumber 3 2 = 19 := rfl

example : MetaMathlibExt.IsSCullenNumber 2 3 := by
  refine ⟨by decide, 1, by decide, ?_⟩
  rfl

example : ¬ MetaMathlibExt.IsSCullenNumber 1 2 := by
  simp [MetaMathlibExt.IsSCullenNumber]

#print axioms MetaMathlibExt.sCullenNumber
#print axioms MetaMathlibExt.IsSCullenNumber

end
