/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction

namespace MetaMathlibExt

example : takagiBit 5 0 = 1 := by decide
example : takagiBit 5 1 = 0 := by decide
example : takagiBit 5 2 = 1 := by decide
example : takagiBit 5 (-1) = 0 := by decide
example : takagiEll 1 0 2 = 1 := by decide

end MetaMathlibExt
