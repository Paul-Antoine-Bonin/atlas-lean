/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.EulerCircuit

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

abbrev triangle := SimpleGraph.cycleGraph 3

theorem connected_hasEulerian_concrete :
    ∃ (u : Fin 3) (p : triangle.Walk u u),
    p.IsTrail ∧ p.edges.countP (0 ∈ ·) = 2 := by
  obtain ⟨u, p, hp⟩ :=
    (SimpleGraph.cycleGraph_connected (n := 2)).exists_isEulerian (by
      intro v
      rw [SimpleGraph.cycleGraph_degree_three_le]
      exact even_two)
  refine ⟨u, p, hp.isTrail, ?_⟩
  rw [hp.countP_edges_eq_degree, SimpleGraph.cycleGraph_degree_three_le]

private theorem zero_mem_triangle_support : (0 : Fin 3) ∈ triangle.support := by
  rw [SimpleGraph.mem_support]
  exact ⟨1, SimpleGraph.cycleGraph_adj.mpr (Or.inr rfl)⟩

private theorem one_mem_triangle_support : (1 : Fin 3) ∈ triangle.support := by
  rw [SimpleGraph.mem_support]
  exact ⟨0, SimpleGraph.cycleGraph_adj.mpr (Or.inl rfl)⟩

example : (triangle.induce triangle.support).Reachable
    ⟨0, zero_mem_triangle_support⟩ ⟨1, one_mem_triangle_support⟩ := by
  have hreach : triangle.Reachable 0 1 :=
    SimpleGraph.cycleGraph_connected (n := 2) 0 1
  exact hreach.induce_support zero_mem_triangle_support one_mem_triangle_support

example : ∃ (u : Fin 3) (p : triangle.Walk u u),
    p.IsTrail ∧ ∀ e ∈ triangle.edgeSet, e ∈ p.edges := by
  have htriangle : triangle.Connected := SimpleGraph.cycleGraph_connected (n := 2)
  have hs : triangle.support = Set.univ := htriangle.preconnected.support_eq_univ
  have hsupport : (triangle.induce triangle.support).Connected := by
    rw [hs]
    exact triangle.induceUnivIso.connected_iff.mpr htriangle
  obtain ⟨u, p, hp⟩ := SimpleGraph.ConnectedSupport.exists_isEulerian hsupport (by
    intro v
    rw [SimpleGraph.cycleGraph_degree_three_le]
    exact even_two)
  exact ⟨u, p, hp.isTrail, fun e he ↦ hp.mem_edges_iff.mpr he⟩

end MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit
