/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Connected.Frontier
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

open Set Topology

/-- Generic API example: a preconnected set crossing a set meets its frontier. -/
example {α : Type*} [TopologicalSpace α] {s A : Set α} (hs : IsPreconnected s)
    (hA : (s ∩ A).Nonempty) (hAc : (s ∩ Aᶜ).Nonempty) :
    (s ∩ frontier A).Nonempty :=
  hs.inter_frontier_nonempty_of_inter_compl hA hAc

/-- Concrete real-interval example crossing both sides of the frontier. -/
example : ((Set.Icc (0 : ℝ) 1) ∩ frontier (Set.Iic (1 / 2))).Nonempty := by
  apply IsPreconnected.inter_frontier_nonempty_of_inter_compl
    isPreconnected_Icc
  · exact ⟨0, left_mem_Icc.mpr (by norm_num), mem_Iic.mpr (by norm_num)⟩
  · refine ⟨1, right_mem_Icc.mpr (by norm_num), ?_⟩
    simp only [mem_compl_iff, mem_Iic, not_le]
    norm_num

end
