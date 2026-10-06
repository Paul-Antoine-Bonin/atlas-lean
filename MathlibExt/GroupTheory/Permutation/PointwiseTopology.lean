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
