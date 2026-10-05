/-
# Homogeneous topological spaces
-/
module

public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-- A topological space is homogeneous if its homeomorphism group acts transitively. -/
class HomogeneousSpace (X : Type*) [TopologicalSpace X] : Prop where
  is_transitive : ∀ x y : X, ∃ f : Homeomorph X X, f x = y
