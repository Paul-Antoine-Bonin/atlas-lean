/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.InducedForestNumber

@[expose] public section

#check @SimpleGraph.inducedForestNumber
#check @SimpleGraph.card_le_inducedForestNumber
#check @SimpleGraph.inducedForestNumber_le_card
#check @SimpleGraph.exists_isAcyclic_card_eq_inducedForestNumber

/-- A two-vertex induced subgraph of the triangle is a tree. -/
private theorem k3_pair_acyclic :
    ((SimpleGraph.completeGraph (Fin 3)).induce
      (↑({0, 1} : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic := by
  rw [SimpleGraph.induce_top]
  apply SimpleGraph.IsAcyclic.of_card_le_two
  have hfin_eq :
      Fintype.card ↥(↑({0, 1} : Finset (Fin 3)) : Set (Fin 3)) = 2 := by
    decide
  have henat_eq :
      ENat.card ↥(↑({0, 1} : Finset (Fin 3)) : Set (Fin 3)) = 2 := by
    rw [ENat.card_eq_coe_fintype_card, hfin_eq]
    simp
  rw [henat_eq]

/-- The full triangle is not a forest: it carries two distinct paths. -/
private theorem k3_univ_not_acyclic :
    ¬ ((SimpleGraph.completeGraph (Fin 3)).induce (Set.univ : Set (Fin 3))).IsAcyclic := by
  rw [SimpleGraph.induce_top]
  intro h
  let a : ↥(Set.univ : Set (Fin 3)) := ⟨0, Set.mem_univ _⟩
  let b : ↥(Set.univ : Set (Fin 3)) := ⟨1, Set.mem_univ _⟩
  let c : ↥(Set.univ : Set (Fin 3)) := ⟨2, Set.mem_univ _⟩
  have hab : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj a b := by
    decide
  have hac : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj a c := by
    decide
  have hcb : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Adj c b := by
    decide
  have hsub :
      Subsingleton
        ((SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp h) _ _
  let w1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b :=
    SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
  let w2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b :=
    SimpleGraph.Walk.cons hac (SimpleGraph.Walk.cons hcb SimpleGraph.Walk.nil)
  have hsup1 : w1.support = [a, b] := rfl
  have hsup2 : w2.support = [a, c, b] := rfl
  have hne_ab : a ≠ b := by decide
  have hne_ac : a ≠ c := by decide
  have hne_cb : c ≠ b := by decide
  have hw1 : w1.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsup1]
    exact List.nodup_cons.mpr ⟨by simp [hne_ab], List.nodup_singleton _⟩
  have hw2 : w2.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hsup2]
    exact List.nodup_cons.mpr ⟨by simp [hne_ac, hne_ab],
      List.nodup_cons.mpr ⟨by simp [hne_cb], List.nodup_singleton _⟩⟩
  let p1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b := ⟨w1, hw1⟩
  let p2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b := ⟨w2, hw2⟩
  have heq : p1 = p2 := @Subsingleton.elim _ hsub _ _
  have hlen := congrArg
    (fun p : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Path a b =>
      ((p : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length)) heq
  have h1 :
      ((p1 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length) = 1 := rfl
  have h2 :
      ((p2 : (SimpleGraph.completeGraph ↥(Set.univ : Set (Fin 3))).Walk a b).length) = 2 := rfl
  omega

example (G : SimpleGraph (Fin 0)) : G.inducedForestNumber = 0 := by
  have hle : G.inducedForestNumber ≤ Fintype.card (Fin 0) :=
    SimpleGraph.inducedForestNumber_le_card G
  simp at hle
  omega

example : (⊥ : SimpleGraph (Fin 3)).inducedForestNumber = 3 := by
  classical
  have hbot : (⊥ : SimpleGraph (Fin 3)).IsAcyclic := by
    simp
  have huniv : ((⊥ : SimpleGraph (Fin 3)).induce
      ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic :=
    hbot.induce ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))
  have hge : (Finset.univ : Finset (Fin 3)).card ≤
      (⊥ : SimpleGraph (Fin 3)).inducedForestNumber :=
    SimpleGraph.card_le_inducedForestNumber _ _ huniv
  have hle : (⊥ : SimpleGraph (Fin 3)).inducedForestNumber ≤ Fintype.card (Fin 3) :=
    SimpleGraph.inducedForestNumber_le_card _
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hcardu : (Finset.univ : Finset (Fin 3)).card = 3 := by simp [hcard]
  omega

example : (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber = 2 := by
  classical
  have h2 : ((SimpleGraph.completeGraph (Fin 3)).induce
      (↑({0, 1} : Finset (Fin 3)) : Set (Fin 3))).IsAcyclic :=
    k3_pair_acyclic
  have hnot : ¬ ((SimpleGraph.completeGraph (Fin 3)).induce
      (Set.univ : Set (Fin 3))).IsAcyclic :=
    k3_univ_not_acyclic
  have hcard01 : ({0, 1} : Finset (Fin 3)).card = 2 := by
    decide
  have hge : 2 ≤ (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber := by
    have hle := SimpleGraph.card_le_inducedForestNumber
      (SimpleGraph.completeGraph (Fin 3)) ({0, 1} : Finset (Fin 3)) h2
    omega
  have hle2 : (SimpleGraph.completeGraph (Fin 3)).inducedForestNumber ≤ 2 := by
    classical
    unfold SimpleGraph.inducedForestNumber
    apply Finset.sup_le
    intro s _
    by_cases h : ((SimpleGraph.completeGraph (Fin 3)).induce (↑s : Set (Fin 3))).IsAcyclic
    · simp only [ite_eq_left h]
      have hcard3 : s.card ≤ 3 := by
        calc s.card ≤ Fintype.card (Fin 3) := Finset.card_le_univ s
          _ = 3 := Fintype.card_fin 3
      by_cases h3 : s.card = 3
      · have hsuniv : s = Finset.univ :=
          Finset.eq_univ_of_card s (h3.trans (Fintype.card_fin 3).symm)
        have hset : (↑s : Set (Fin 3)) = Set.univ := by
          rw [hsuniv, Finset.coe_univ]
        exact absurd (hset ▸ h) hnot
      · omega
    · simp only [ite_eq_right h]
      exact Nat.zero_le _
  omega

end
