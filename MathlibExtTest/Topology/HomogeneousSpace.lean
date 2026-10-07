/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.HomogeneousSpace

example {X : Type*} [TopologicalSpace X] [HomogeneousSpace X] (x y : X) :
    ∃ f : Homeomorph X X, f x = y :=
  HomogeneousSpace.is_transitive x y

/-- Every subsingleton topological space is homogeneous. -/
example (X : Type*) [TopologicalSpace X] [Subsingleton X] : HomogeneousSpace X where
  is_transitive x y := ⟨Homeomorph.refl X, Subsingleton.elim x y⟩

#print axioms HomogeneousSpace
