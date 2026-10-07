/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions

namespace Equiv.Perm

@[expose] public section

/-- The pointwise-convergence topology on permutations: the topology induced by the
evaluation map into `α → α`, where `α` is discrete and the function space carries the
product topology. Kept as a named definition (not an instance) so callers supply it
explicitly. -/
noncomputable abbrev pointwiseTopology {α : Type*} : TopologicalSpace (Equiv.Perm α) :=
  letI : TopologicalSpace α := ⊥
  TopologicalSpace.induced (fun σ : Equiv.Perm α => ⇑σ) inferInstance

end

end Equiv.Perm
