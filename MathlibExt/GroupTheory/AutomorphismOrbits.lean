/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Defs

namespace MetaMathlibExt

@[expose] public section

/-- The full automorphism group has finitely many orbits on the elements of the group. -/
def HasFinitelyManyAutomorphismOrbits (G : Type*) [Group G] : Prop :=
  Finite (MulAction.orbitRel.Quotient (MulAut G) G)

end

end MetaMathlibExt
