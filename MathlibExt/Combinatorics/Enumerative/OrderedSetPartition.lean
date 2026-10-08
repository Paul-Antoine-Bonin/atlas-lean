/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt

/-- Ordered set partition (set composition) of `V`: a list of nonempty blocks
partitioning `V`, i.e. an element of `(SpList ∘ SpSet₊)[V]`
(source statement `jis_0874746b31275e17727c6370`,
concept `jis_sem_de11a43abe164463205fe64c`). -/
def IsOrderedSetPartition {α : Type*} [DecidableEq α] (V : Finset α)
    (blocks : List (Finset α)) : Prop :=
  (∀ B ∈ blocks, B.Nonempty) ∧
    (∀ B ∈ blocks, B ⊆ V) ∧
    blocks.Pairwise (fun A B => Disjoint A B) ∧
    V = blocks.foldl (· ∪ ·) ∅

end MetaMathlibExt
