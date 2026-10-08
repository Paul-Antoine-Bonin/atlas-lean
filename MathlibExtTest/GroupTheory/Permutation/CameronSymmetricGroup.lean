/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.CameronSymmetricGroup

@[expose] public section

/-!
# Tests for the Cameron symmetric-group representative `S`

Compile-time checks for `isHighlyHomogeneous_top` and both projections of
`cameron_symmetricGroup_closed_highlyHomogeneous`. These examples exercise the
statements only; they do not duplicate the proofs.
-/

namespace CameronSymmetricGroupTest

/-- The generic top-subgroup theorem applies on any carrier. -/
example {α : Type*} [DecidableEq α] :
    MetaMathlibExt.IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm α)) :=
  MetaMathlibExt.isHighlyHomogeneous_top

/-- The generic top-subgroup theorem applies to the rationals. -/
example : MetaMathlibExt.IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm ℚ)) :=
  MetaMathlibExt.isHighlyHomogeneous_top

/-- The closedness projection of the Cameron conjunction. -/
example : @IsClosed (Equiv.Perm ℚ) (Equiv.Perm.pointwiseTopology (α := ℚ))
    (↑(⊤ : Subgroup (Equiv.Perm ℚ)) : Set (Equiv.Perm ℚ)) :=
  MetaMathlibExt.cameron_symmetricGroup_closed_highlyHomogeneous.1

/-- The homogeneity projection of the Cameron conjunction. -/
example : MetaMathlibExt.IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm ℚ)) :=
  MetaMathlibExt.cameron_symmetricGroup_closed_highlyHomogeneous.2

end CameronSymmetricGroupTest
