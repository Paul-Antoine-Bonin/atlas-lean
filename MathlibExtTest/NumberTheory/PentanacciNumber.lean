/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PentanacciNumber

namespace MetaMathlibExt

example : pentanacciNumber 0 = 1 := rfl
example : pentanacciNumber 4 = 8 := rfl
example : pentanacciNumber 5 = 16 := rfl
example : pentanacciNumber 6 = 31 := rfl

#print axioms pentanacciNumber

end MetaMathlibExt
