/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.FleischnerStrong

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong

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

theorem complete_three_hasStrongSquareCycle :
    ∃ p : (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0,
    p.IsHamiltonianCycle ∧ p.length = 3 ∧
      (⊤ : SimpleGraph (Fin 3)).Adj 0 p.snd ∧
      (⊤ : SimpleGraph (Fin 3)).Adj p.penultimate 0 := by
  obtain ⟨p, hp, hfirst, hlast⟩ :=
    completeGraph_isVertexConnected_two.hasStrongSquareCycle 0
  have hlength :=
    (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mp hp).2
  exact ⟨p, hp, by simpa using hlength, hfirst, hlast⟩

end MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong
