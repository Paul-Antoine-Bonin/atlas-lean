/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial

namespace MetaMathlibExt

example : partialBellPolynomial 0 0 (fun _ => (1 : ℕ)) = 1 := by decide
example : partialBellPolynomial 3 2 (fun _ => (1 : ℕ)) = 3 := by decide

end MetaMathlibExt
