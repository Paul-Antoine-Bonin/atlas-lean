/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Homogeneous topological spaces
-/
module

public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-- A topological space is homogeneous if its homeomorphism group acts transitively. -/
class HomogeneousSpace (X : Type*) [TopologicalSpace X] : Prop where
  is_transitive : ∀ x y : X, ∃ f : Homeomorph X X, f x = y
