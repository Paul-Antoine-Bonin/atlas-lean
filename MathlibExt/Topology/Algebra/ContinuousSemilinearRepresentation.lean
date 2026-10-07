/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

/-!
# Continuous semilinear representations

This file records the object-level data of a continuous semilinear group representation on a
finite free module over a topological ring.

The topology on the module is required to be the finite product topology transported through the
coordinates of `Module.Free.chooseBasis`.
-/

/-- A finite free `R`-module whose topology is transported from `R`, equipped with a continuous
semilinear action of the topological group `G`.

This is the object-level content of Definition `defsemilinrep` in arXiv:2608.00845, lines
1947–1950. The inherited `SMulDistribClass G R M` is the semilinearity identity
`g • (r • x) = (g • r) • (g • x)`.
-/
class IsContinuousSemilinearRepresentation (G R M : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    [MulSemiringAction G R] [DistribMulAction G M]
    [ContinuousSMul G R] [ContinuousSMul G M] [ContinuousSMul R M] : Prop
    extends SMulDistribClass G R M where
  /-- The topology on `M` is the product topology transported through coordinates in a finite
  `R`-basis. -/
  isHomeomorph_equivFun : IsHomeomorph (Module.Free.chooseBasis R M).equivFun

end
