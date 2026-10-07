/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace SimpleGraph

/-- A graph is vertex-transitive when its automorphism group acts transitively
on vertices. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : G ≃g G, e u = v

@[simp] theorem isVertexTransitive_of_subsingleton {V : Type*} [Subsingleton V]
    (G : SimpleGraph V) : G.IsVertexTransitive := by
  intro u v
  exact ⟨SimpleGraph.Iso.refl, Subsingleton.elim _ _⟩

end SimpleGraph
