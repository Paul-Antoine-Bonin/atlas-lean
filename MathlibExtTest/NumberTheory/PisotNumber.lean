/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PisotNumber

namespace MetaMathlibExt

example {q : ℝ} (hq : IsPisotNumber q) : IsIntegral ℤ q := hq.1
example {q : ℝ} (hq : IsPisotNumber q) : 1 < q := hq.2.1

end MetaMathlibExt
