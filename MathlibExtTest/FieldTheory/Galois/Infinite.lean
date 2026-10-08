/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Galois.Infinite

set_option autoImplicit false

open InfiniteGalois

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- The new closure theorem fires generically. -/
example (H : Subgroup Gal(K/k)) :
    H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup :=
  topologicalClosure_eq_fixingSubgroup_fixedField H

/-- Closed subgroups are recovered from their fixed field. -/
example (H : Subgroup Gal(K/k)) (hH : IsClosed (H : Set Gal(K/k))) :
    (IntermediateField.fixedField H).fixingSubgroup = H := by
  have hclose : H.topologicalClosure = H :=
    le_antisymm (Subgroup.topologicalClosure_minimal H le_rfl hH)
      (Subgroup.le_topologicalClosure H)
  rw [← topologicalClosure_eq_fixingSubgroup_fixedField H, hclose]
