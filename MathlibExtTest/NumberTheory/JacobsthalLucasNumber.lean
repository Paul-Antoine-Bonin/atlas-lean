/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JacobsthalLucasNumber

@[expose] public section

namespace MetaMathlibExt

example : jacobsthalLucasNumber 0 = 2 := rfl
example : jacobsthalLucasNumber 1 = 1 := rfl
example : jacobsthalLucasNumber 2 = 5 := rfl
example : jacobsthalLucasNumber 3 = 7 := rfl
example : jacobsthalLucasNumber 4 = 17 := rfl
example : jacobsthalLucasNumber 5 = 31 := rfl

example (n : ℕ) :
    jacobsthalLucasNumber (n + 2) =
      jacobsthalLucasNumber (n + 1) + 2 * jacobsthalLucasNumber n := rfl

#print axioms MetaMathlibExt.jacobsthalLucasNumber

end MetaMathlibExt

end
