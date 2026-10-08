/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Metrizable.Uniformity

@[expose] public section

/-!
# Birkhoff–Kakutani metrization theorem
-/

noncomputable section

namespace MathlibExt.Topology.Algebra.BirkhoffKakutani

/--
Every Hausdorff first-countable topological group is metrizable.
Source: G. Birkhoff, Compositio Math. 3 (1936), 427-430; S. Kakutani, Proc. Imp. Acad. Tokyo 12
(1936), 4-7, DOI 10.3792/PIA/1195580206.
Proves `Wanted` entry `birkhoff_kakutani_metrization`.
-/
theorem birkhoff_kakutani_metrization
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [FirstCountableTopology G] :
    TopologicalSpace.MetrizableSpace G := by
  have hU : Filter.IsCountablyGenerated
      (@uniformity G (IsTopologicalGroup.leftUniformSpace G)) := by
    change Filter.IsCountablyGenerated
      (Filter.comap (fun p : G × G => p.1⁻¹ * p.2) (nhds 1))
    infer_instance
  have hT0 : T0Space G := inferInstance
  exact @UniformSpace.metrizableSpace _ (IsTopologicalGroup.leftUniformSpace G) hU hT0

end MathlibExt.Topology.Algebra.BirkhoffKakutani
