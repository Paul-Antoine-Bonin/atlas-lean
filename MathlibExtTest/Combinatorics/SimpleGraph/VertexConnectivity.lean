/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

@[expose] public section

example {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ¬ SimpleGraph.IsVertexConnected (Fintype.card V) G :=
  fun h => Nat.lt_irrefl _ h.1

example : ¬ SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 2)) := by
  intro h
  have hc : Fintype.card (Fin 2) = 2 := by simp
  have hlt := h.1
  omega

example (n : ℕ) : SimpleGraph.IsVertexConnected 0 (⊤ : SimpleGraph (Fin (n + 1))) where
  left := by simp
  right := fun S hS => False.elim (Nat.not_lt_zero _ hS)

example : SimpleGraph.IsVertexConnected 1 (⊤ : SimpleGraph (Fin 2)) := by
  rw [SimpleGraph.isVertexConnected_iff]
  refine ⟨by decide, ?_⟩
  intro S hS
  have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst S
  let _ : Nonempty
      {x : Fin 2 // x ∈ (↑(∅ : Finset (Fin 2)) : Set (Fin 2))ᶜ} :=
    ⟨⟨0, by simp⟩⟩
  rw [SimpleGraph.induce_top]
  exact SimpleGraph.connected_top

namespace MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity

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

example : SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 4)) :=
  completeGraph_isVertexConnected_two

example : 3 ≤ Fintype.card (Fin 4) := by
  have hcard := completeGraph_isVertexConnected_two.card_gt
  omega

example :
    ((⊤ : SimpleGraph (Fin 4)).induce
      (↑({0} : Finset (Fin 4)) : Set (Fin 4))ᶜ).Reachable
      ⟨1, by simp⟩ ⟨2, by simp⟩ := by
  exact completeGraph_isVertexConnected_two.connected_induce_compl {0} (by decide) _ _

example : (⊤ : SimpleGraph (Fin 4)).Reachable 0 3 := by
  exact completeGraph_isVertexConnected_two.connected (by omega) 0 3

example :
    ((⊤ : SimpleGraph (Fin 4)).induce
      (↑({0} : Finset (Fin 4)) : Set (Fin 4))ᶜ).Reachable
      ⟨1, by simp⟩ ⟨3, by simp⟩ := by
  exact completeGraph_isVertexConnected_two.connected_compl_singleton (by omega) 0 _ _

example : 2 ≤ (⊤ : SimpleGraph (Fin 4)).degree 0 :=
  completeGraph_isVertexConnected_two.two_le_degree 0

theorem complete_four_has_cycle_through :
    ∃ c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0,
    c.IsCycle ∧ 3 ≤ c.length := by
  obtain ⟨c, hc⟩ := completeGraph_isVertexConnected_two.exists_cycle_through 0
  exact ⟨c, hc, hc.three_le_length⟩

end MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity
