/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.GeneralizedRegularExpression

@[expose] public section

/-!
# Client tests for generalized regular expressions

Smoke tests for `regularStarHeight`, `GenRegExp.denote` / `starHeight`,
and `HasGenHeightLe`.
-/

namespace Cslib.Language

example : regularStarHeight (RegularExpression.char 'a') = 0 := rfl

example : regularStarHeight (RegularExpression.star (RegularExpression.char 'a')) = 1 := rfl

example :
    regularStarHeight
      (RegularExpression.plus (RegularExpression.char 'a')
        (RegularExpression.star (RegularExpression.char 'b'))) = 1 := rfl

example : GenRegExp.starHeight (GenRegExp.ofReg (RegularExpression.char 'a')) = 0 := rfl

example :
    GenRegExp.starHeight
      (GenRegExp.star (GenRegExp.compl (GenRegExp.ofReg (RegularExpression.char 'a')))) = 1 := rfl

example :
    (GenRegExp.ofReg (RegularExpression.char 'a')).denote = {['a']} := rfl

example : HasGenHeightLe (α := Char) {['a']} 0 :=
  ⟨GenRegExp.ofReg (RegularExpression.char 'a'), rfl, le_refl 0⟩

end Cslib.Language
