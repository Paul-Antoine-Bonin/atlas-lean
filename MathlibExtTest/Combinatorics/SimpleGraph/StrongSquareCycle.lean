/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.StrongSquareCycle

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

private theorem adj_zero_one :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 0 1 :=
  ⟨by decide, Or.inl (by simp)⟩

private theorem adj_one_two :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 1 2 :=
  ⟨by decide, Or.inl (by simp)⟩

private theorem adj_two_zero :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 2 0 :=
  ⟨by decide, Or.inl (by simp)⟩

private def triangleWalk :
    (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0 :=
  .cons adj_zero_one (.cons adj_one_two (.cons adj_two_zero .nil))

theorem complete_three_hasStrongSquareCycle :
    (⊤ : SimpleGraph (Fin 3)).HasStrongSquareCycle 0 := by
  have hcycle : triangleWalk.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [SimpleGraph.Walk.isPath_def, triangleWalk]
  have hhamiltonian : triangleWalk.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hcycle, by simp [triangleWalk]⟩
  refine ⟨triangleWalk, hhamiltonian, ?_, ?_⟩ <;> simp [triangleWalk]

example :
    ∃ p : (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0, p.IsHamiltonianCycle := by
  obtain ⟨p, hp, -, -⟩ :=
    (SimpleGraph.hasStrongSquareCycle_iff (⊤ : SimpleGraph (Fin 3)) 0).mp
      complete_three_hasStrongSquareCycle
  exact ⟨p, hp⟩

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle
