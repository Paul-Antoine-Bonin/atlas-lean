/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConwayHofstadterLikeSequence
import Mathlib.Tactic

namespace MetaMathlibExt

example : conwayHofstadterResidue 6 3 = 3 := by
  decide

example : conwayHofstadterResidue 7 3 = 1 := by
  decide

example {c : ℕ → ℕ} (h : IsConwayHofstadterLikeSequence 2 c) : c 3 = 2 := by
  simpa [conwayHofstadterResidue, h.1, h.2.1] using h.2.2 3 (by omega)

#print axioms conwayHofstadterResidue
#print axioms IsConwayHofstadterLikeSequence

end MetaMathlibExt
