/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Fleischner

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.Fleischner

private theorem completeGraph_isVertexConnected_two :
    SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 3)) := by
  rw [SimpleGraph.isVertexConnected_two_iff]
  refine ⟨by decide, SimpleGraph.connected_top, ?_⟩
  intro v
  rw [SimpleGraph.induce_top]
  let _ : Nonempty {x : Fin 3 // x ∈ (↑({v} : Finset (Fin 3)) : Set (Fin 3))ᶜ} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set]
      simp)
  exact SimpleGraph.connected_top

theorem fleischner_complete_three :
    ∃ (x : Fin 3) (p : (⊤ : SimpleGraph (Fin 3)).Walk x x),
    @SimpleGraph.Walk.IsHamiltonianCycle (Fin 3)
      (fun a b ↦ Classical.propDecidable (a = b)) _ x p ∧ p.length = 3 := by
  classical
  have hhamiltonian := MetaMathlibExt.fleischner
    (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3))
    completeGraph_isVertexConnected_two (by
      intro u v
      simp only [SimpleGraph.top_adj]
      constructor
      · intro huv
        exact ⟨huv, Or.inl huv⟩
      · exact fun h ↦ h.1)
  obtain ⟨x, p, hp⟩ := hhamiltonian (by decide)
  have hlength :=
    ((@SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq
      (Fin 3) (fun a b ↦ Classical.propDecidable (a = b))
      (⊤ : SimpleGraph (Fin 3)) x p inferInstance).mp hp).2
  exact ⟨x, p, hp, by simpa using hlength⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Fleischner
