/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PisotRoot

namespace MetaMathlibExt

example {P : Polynomial ℝ} {r : ℝ} (h : IsUniquePisotRoot P r) : P.IsRoot r := h.2.1

example {P : Polynomial ℝ} {r s : ℝ} (hr : IsUniquePisotRoot P r)
    (hs : IsPisotNumber s) (hPs : P.IsRoot s) : s = r :=
  hr.2.2 s hs hPs

end MetaMathlibExt
