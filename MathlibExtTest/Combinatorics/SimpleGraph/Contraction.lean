/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Contraction

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.Contraction

abbrev retained : Set (Fin 4) := {0, 1}

def zero : retained := ⟨0, by simp [retained]⟩

private def one : retained := ⟨1, by simp [retained]⟩

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

theorem collapseOutside_concrete : SimpleGraph.collapseOutside retained 0 = some zero ∧
    SimpleGraph.collapseOutside retained 2 = none := by
  constructor
  · exact SimpleGraph.collapseOutside_of_mem retained (by simp [retained])
  · exact SimpleGraph.collapseOutside_of_notMem retained (by simp [retained])

example : SimpleGraph.collapseOutside retained 1 = some one := by
  exact SimpleGraph.collapseOutside_of_mem retained (by simp [retained])

example : SimpleGraph.collapseOutside retained 3 = none := by
  exact SimpleGraph.collapseOutside_of_notMem retained (by simp [retained])

example : SimpleGraph.collapseOutside retained 1 ≠ some zero := by
  intro h
  have hval := congrArg Fin.val
    (SimpleGraph.collapseOutside_eq_some_iff retained 1 zero |>.mp h)
  change 1 = 0 at hval
  omega

example : SimpleGraph.collapseOutside retained 0 ≠ none := by
  intro h
  have hout := SimpleGraph.collapseOutside_eq_none_iff retained 0 |>.mp h
  exact hout (by simp [retained])

example : ∃ v : Fin 4, SimpleGraph.collapseOutside retained v = none := by
  exact SimpleGraph.collapseOutside_surjective
    (D := retained) ⟨2, by simp [retained]⟩ none

example : ((⊤ : SimpleGraph (Fin 4)).contractOutside retained).Adj
    (some zero) (some one) := by
  rw [SimpleGraph.contractOutside_adj_some]
  simp [zero, one]

example : ((⊤ : SimpleGraph (Fin 4)).contractOutside retained).Adj
    (some zero) none := by
  rw [SimpleGraph.contractOutside_adj_none]
  exact ⟨2, by simp [retained], by simp [zero]⟩

example : 2 < Fintype.card (Option retained) := by
  have hconnected : ((⊤ : SimpleGraph (Fin 4)).induce retained).Connected := by
    rw [SimpleGraph.induce_top]
    let _ : Nonempty retained := ⟨zero⟩
    exact SimpleGraph.connected_top
  have hout : retainedᶜ.Nonempty := ⟨2, by simp [retained]⟩
  have hcontract := completeGraph_isVertexConnected_two.contractOutside
    (D := retained) (by simp [retained]) hconnected hout
  exact hcontract.card_gt

example : Fintype.card (Option retained) < Fintype.card (Fin 4) := by
  apply SimpleGraph.card_contractOutside_lt retained
  rw [Fintype.card_compl_set]
  simp [retained]

end MathlibExtTest.Combinatorics.SimpleGraph.Contraction
