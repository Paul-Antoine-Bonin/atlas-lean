/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch8Entry19Gaussdigamma

@[expose] public section

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch8Entry19Gaussdigamma

open Filter Topology
open MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry19Gaussdigamma

-- Entry 19 identifies the constant term of the ordinary counting sum with ζ(0) = -1/2.
example :
    Tendsto (chapter8LogPowerConstantApprox 0) atTop (𝓝 (-1 / 2 : ℝ)) := by
  have h := (ramanujan_part1_ch8_entry19_gaussdigamma 1).1 0 (by omega)
  simpa [chapter8LogPowerConstant, riemannZeta_zero] using h

end MathlibExtTest.Analysis.Ramanujan.Part1Ch8Entry19Gaussdigamma
