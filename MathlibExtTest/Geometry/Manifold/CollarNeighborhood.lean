/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.CollarNeighborhood

open Manifold Set
open scoped Manifold

open MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

-- The collar image is an open neighborhood of the manifold boundary.
example {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ∃ U : Set M, IsOpen U ∧ ModelWithCorners.boundary (I := 𝓡∂ n) M ⊆ U := by
  obtain ⟨c, hc, hzero⟩ :=
    topological_collar_neighborhood_of_smooth_manifold_with_boundary (n := n) (M := M)
  refine ⟨range c, hc.isOpen_range, ?_⟩
  intro x hx
  let b : ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M) := ⟨x, hx⟩
  exact ⟨(b, ⟨0, by simp⟩), hzero b⟩
