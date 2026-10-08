/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.OddIndependent
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Odd independent set tests

Checks the empty/singleton theorems and separates independence from the
parity condition on the three-vertex path.
-/

@[expose] public section

/-- Empty and singleton sanity checks for odd independence. -/
example : (SimpleGraph.pathGraph 3).IsOddIndependent ∅ :=
  (SimpleGraph.pathGraph 3).isOddIndependent_empty

example (a : Fin 3) : (SimpleGraph.pathGraph 3).IsOddIndependent {a} :=
  (SimpleGraph.pathGraph 3).isOddIndependent_singleton a

namespace PathGraph3OddTest

/-- Endpoints of `P₃` are independent. -/
private theorem endpoints_indep :
    (SimpleGraph.pathGraph 3).IsIndepSet ({0, 2} : Set (Fin 3)) := by
  classical
  intro u hu w hw hne hadj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd rfl hne
  · have h02 : ¬ (SimpleGraph.pathGraph 3).Adj 0 2 := by rw [SimpleGraph.pathGraph_adj]; omega
    exact absurd hadj h02
  · have h20 : ¬ (SimpleGraph.pathGraph 3).Adj 2 0 := by rw [SimpleGraph.pathGraph_adj]; omega
    exact absurd hadj h20
  · exact absurd rfl hne

/-- Endpoints of `P₃` fail odd independence at the middle vertex. -/
private theorem endpoints_not_odd :
    ¬ (SimpleGraph.pathGraph 3).IsOddIndependent ({0, 2} : Set (Fin 3)) := by
  classical
  intro h
  have h1not : (1 : Fin 3) ∉ ({0, 2} : Set (Fin 3)) := by decide
  obtain ⟨_, h2⟩ := h
  obtain ⟨_, heither⟩ := h2 1 h1not
  have h10 : (SimpleGraph.pathGraph 3).Adj 1 0 := by rw [SimpleGraph.pathGraph_adj]; omega
  have h12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by rw [SimpleGraph.pathGraph_adj]; omega
  have hsub : ({0, 2} : Set (Fin 3)) ⊆
      (SimpleGraph.pathGraph 3).neighborSet 1 := by
    rw [Set.insert_subset_iff]
    constructor
    · rw [SimpleGraph.mem_neighborSet]
      exact h10
    · rw [Set.singleton_subset_iff]
      rw [SimpleGraph.mem_neighborSet]
      exact h12
  have hinter : (SimpleGraph.pathGraph 3).neighborSet 1 ∩
      ({0, 2} : Set (Fin 3)) = {0, 2} :=
    Set.inter_eq_self_of_subset_right hsub
  rw [hinter] at heither
  rcases heither with hempty | hodd
  · have hmem : (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by decide
    rw [hempty] at hmem
    exact Set.notMem_empty 0 hmem
  · have hne : (0 : Fin 3) ≠ 2 := by decide
    have hcard : (({0, 2} : Set (Fin 3))).ncard = 2 := Set.ncard_pair hne
    rw [hcard] at hodd
    exact absurd hodd (by decide)

end PathGraph3OddTest
