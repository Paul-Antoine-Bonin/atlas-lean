/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OddLichtenbergNumbers

namespace MetaMathlibExt

example : List.map oddLichtenberg [0, 1, 2, 3] = [1, 5, 21, 85] := by rfl

end MetaMathlibExt
