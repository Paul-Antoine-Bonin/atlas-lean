/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.SaturatingNonedge
import Mathlib.Tactic.FinCases

/-!
# Boundary tests for `F`-saturating non-edges

Source: Xiaolin Wang, Jiabao Yang, and Ruilin Zheng,
*Clique-saturating non-edges throughout the Turan range*, arXiv:2608.25831v1.
Active source: `main.tex`, lines 89-99.

These tests exercise every public declaration of
`MathlibExt.Combinatorics.SimpleGraph.SaturatingNonedge` against the
source-sensitive boundaries: a single missing edge that creates a copy, a loop
rejection (discriminating for distinctness), an already-present edge rejection
(discriminating for absence), distinct absent endpoints with no created copy
(discriminating for copy containment), symmetry, the new-copy consequence, the
saturating graph, and the finite counts `1` and `0`.
-/

open SimpleGraph

/-- The complete graph sits below the empty graph plus the single missing edge. -/
theorem test_le :
    (⊤ : SimpleGraph (Fin 2)) ≤ (⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1 := by
  intro a b h
  rw [top_adj] at h
  fin_cases a <;> fin_cases b
  · exact absurd rfl h
  · rw [sup_adj]
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩)
  · rw [sup_adj]
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, by decide⟩)
  · exact absurd rfl h

/-- The single missing edge of the empty graph on two vertices creates a copy. -/
theorem test_creates_copy :
    IsContained (⊤ : SimpleGraph (Fin 2))
      ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) :=
  IsContained.of_le test_le

/-- A single missing edge that creates a copy is saturating, via the characterization. -/
theorem test_single_missing_edge :
    IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2))
      (0 : Fin 2) 1 := by
  rw [isSaturatingNonedge_iff]
  exact ⟨by decide, by decide, test_creates_copy⟩

/-- Symmetry gives the mirror non-edge. -/
theorem test_symm_edge :
    IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2))
      (1 : Fin 2) 0 :=
  test_single_missing_edge.symm

/-- At the loop, non-adjacency holds, so loop rejection must use distinctness. -/
theorem test_loop_not_adj :
    ¬(⊤ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 0 := by
  decide

/-- At the loop, containment holds since the empty graph sits below any host. -/
theorem test_loop_contained :
    IsContained (⊥ : SimpleGraph (Fin 2))
      ((⊤ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 0) :=
  IsContained.of_le bot_le

/-- A loop is not a source-level non-edge, so it is never saturating.
The other two conjuncts hold at `x = y` (see `test_loop_not_adj` and
`test_loop_contained`), hence this rejection depends on `x ≠ y`: deleting that
conjunct would make the predicate true here. -/
theorem test_loop_rejection :
    ¬IsSaturatingNonedge (⊥ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2))
      (0 : Fin 2) 0 :=
  fun h => (h.ne) rfl

/-- At the present edge, distinctness holds, so that rejection must use absence. -/
theorem test_present_ne : (0 : Fin 2) ≠ 1 := by
  decide

/-- At the present edge, containment holds since the host sits below the sup. -/
theorem test_present_contained :
    IsContained (⊤ : SimpleGraph (Fin 2))
      ((⊤ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) :=
  IsContained.of_le le_sup_left

/-- An already-present edge is not a non-edge, so it is never saturating.
The other two conjuncts hold here (see `test_present_ne` and
`test_present_contained`), hence this rejection depends on `¬ G.Adj x y`. -/
theorem test_present_edge_rejection :
    ¬IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2))
      (0 : Fin 2) 1 :=
  fun h => (h.not_adj) (by decide)

/-- At the copy-free probe, distinctness holds, so rejection must use containment. -/
theorem test_nocopy_ne : (0 : Fin 2) ≠ 1 := by
  decide

/-- At the copy-free probe, absence holds, so rejection must use containment. -/
theorem test_nocopy_not_adj :
    ¬(⊥ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 1 := by
  decide

/-- A single edge on two vertices cannot host the edgeless graph on three
vertices, by the vertex-count characterization of `⊥` containment. -/
theorem test_nocopy_not_contained :
    ¬IsContained (⊥ : SimpleGraph (Fin 3))
      ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) := by
  rw [bot_isContained_iff_card_le]
  decide

/-- Distinct absent endpoints need not create a copy, so they are not saturating.
The other two conjuncts hold here (see `test_nocopy_ne` and
`test_nocopy_not_adj`), hence this rejection depends on the copy-containment
conjunct: deleting it would make the predicate true here. -/
theorem test_nocopy_rejection :
    ¬IsSaturatingNonedge (⊥ : SimpleGraph (Fin 3)) (⊥ : SimpleGraph (Fin 2))
      (0 : Fin 2) 1 :=
  fun h => test_nocopy_not_contained h.2.2

/-- The empty host is `⊤`-free, recording the source's contextual hypothesis. -/
theorem test_free_host : Free (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) :=
  free_bot (by
    intro h
    have hadj : (⊤ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 1 :=
      (top_adj _ _).mpr (by decide)
    rw [h] at hadj
    exact (bot_adj _ _).mp hadj)

/-- Under the `F`-free hypothesis, the saturating non-edge creates a new copy. -/
theorem test_new_copy :
    IsContained (⊤ : SimpleGraph (Fin 2))
        ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) ∧
      ¬IsContained (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) :=
  IsSaturatingNonedge.newCopy_of_free _ _ test_single_missing_edge test_free_host

/-- The saturating graph here is exactly the single missing edge. -/
theorem test_graph_eq_single :
    saturatingNonedgeGraph (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) =
      edge (0 : Fin 2) 1 := by
  ext a b
  rw [saturatingNonedgeGraph_adj]
  constructor
  · intro h
    have hne : a ≠ b := h.ne
    rw [edge_adj]
    refine ⟨?_, hne⟩
    fin_cases a <;> fin_cases b <;> simp_all
  · intro h
    rw [edge_adj] at h
    obtain ⟨hmem, hne⟩ := h
    fin_cases a <;> fin_cases b
    · exact absurd rfl hne
    · exact test_single_missing_edge
    · exact test_symm_edge
    · exact absurd rfl hne

-- Finite edge data, section-scoped to the count-one theorem below.
section CountOne

noncomputable local instance instCountOne (G : SimpleGraph (Fin 2)) :
    Fintype G.edgeSet := by
  classical
  exact fintypeEdgeSet _

/-- Finite count `1`: one saturating non-edge. -/
theorem test_count_one :
    numSaturatingNonedges (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) = 1 := by
  rw [numSaturatingNonedges_eq_card_edgeFinset, test_graph_eq_single]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hfin : (edge (0 : Fin 2) 1).edgeFinset = {s((0 : Fin 2), 1)} := by
    simp [edgeFinset, edgeSet_edge_of_ne h01]
  rw [hfin]
  simp

end CountOne

/-- With every edge present, no non-edge is saturating. -/
theorem test_graph_eq_empty :
    saturatingNonedgeGraph (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) =
      ⊥ := by
  ext a b
  rw [saturatingNonedgeGraph_adj]
  constructor
  · intro h
    exact absurd ((top_adj a b).mpr h.ne) h.not_adj
  · intro h
    exact False.elim ((bot_adj a b).mp h)

-- Finite edge data, section-scoped to the count-zero theorem below.
section CountZero

noncomputable local instance instCountZero (G : SimpleGraph (Fin 2)) :
    Fintype G.edgeSet := by
  classical
  exact fintypeEdgeSet _

/-- Finite count `0`: no saturating non-edges. -/
theorem test_count_zero :
    numSaturatingNonedges (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) = 0 := by
  rw [numSaturatingNonedges_eq_card_edgeFinset, test_graph_eq_empty]
  simp

end CountZero
