/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ThreeSumset

open scoped Pointwise

namespace MetaMathlibExt

example (A B C : Finset (ZMod 5)) :
    ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card :=
  gyarmatiMatolcsiRuzsa_three_sumset_zmod 5 (by decide) (by decide) A B C

end MetaMathlibExt
