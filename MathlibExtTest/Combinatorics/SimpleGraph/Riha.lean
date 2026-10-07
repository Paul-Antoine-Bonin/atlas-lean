/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Riha

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.Riha

private theorem completeGraph_isVertexConnected_two :
    SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 4)) := by
  rw [SimpleGraph.isVertexConnected_two_iff]
  refine ⟨by decide, SimpleGraph.connected_top, ?_⟩
  intro v
  rw [SimpleGraph.induce_top]
  let _ : Nonempty {x : Fin 4 // x ∈ (↑({v} : Finset (Fin 4)) : Set (Fin 4))ᶜ} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set]
      simp)
  exact SimpleGraph.connected_top

theorem riha_complete_four :
    ∃ (c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0) (y : Fin 4),
    c.IsCycle ∧ y ≠ 0 ∧ y ∈ c.support ∧
      ((⊤ : SimpleGraph (Fin 4)).Adj y 3 → 3 ∈ c.support) := by
  obtain ⟨c, hc, y, hy, hbound⟩ :=
    completeGraph_isVertexConnected_two.exists_cycle_bound_vertex 0
  exact ⟨c, y, hc, hy, hbound.1, fun hy3 ↦ hbound.2 hy3⟩

example :
    ∃ (c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0) (y : Fin 4),
      y ≠ 0 ∧ ∀ ⦃z⦄, (⊤ : SimpleGraph (Fin 4)).Adj y z → z ∈ c.support := by
  obtain ⟨c, -, y, hy, hbound⟩ :=
    completeGraph_isVertexConnected_two.exists_cycle_bound_vertex 0
  have hbound' := (SimpleGraph.Walk.isBoundVertex_iff c y).mp hbound
  exact ⟨c, y, hy, hbound'.2⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Riha
