module

import MathlibExt.Combinatorics.SimpleGraph.Expander
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace SimpleGraph.ExpanderTest

example : (1 : Fin 4) ∈
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
  simp only [SimpleGraph.mem_externalNeighborSet]
  exact ⟨by decide, 0, by decide, by decide⟩

example : (0 : Fin 4) ∉
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
  simp only [SimpleGraph.mem_externalNeighborSet, not_and]
  intro h _
  exact h (by decide)

example : Disjoint
    ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}) {0} :=
  SimpleGraph.externalNeighborSet_disjoint _ _

example : ∃ a ∈ ({0, 2} : Set (Fin 4)),
    (SimpleGraph.completeGraph (Fin 4)).Adj a 1 := by
  have hmem : (1 : Fin 4) ∈
      (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0, 2} := by
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 0, by decide, by decide⟩
  exact SimpleGraph.exists_adj_of_mem_externalNeighborSet _ hmem

private theorem card_threshold :
    (Nat.card (Fin 4) : ℝ) / (2 * (1 : ℝ)) = 2 := by
  have hc : Nat.card (Fin 4) = 4 := by simp
  rw [hc]
  norm_num

private theorem one_le_external_singleton (a : Fin 4) :
    (1 : ℝ) ≤
      (((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {a}).ncard :
        ℝ) := by
  fin_cases a
  · have hsub : ({1} : Set (Fin 4)) ⊆
        (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SimpleGraph.mem_externalNeighborSet]
      exact ⟨by decide, 0, by decide, by decide⟩
    have hle : ({1} : Set (Fin 4)).ncard ≤
        ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
        ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :
          ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
        (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1} := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SimpleGraph.mem_externalNeighborSet]
      exact ⟨by decide, 1, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
        ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
        ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1}).ncard :
          ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
        (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2} := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SimpleGraph.mem_externalNeighborSet]
      exact ⟨by decide, 2, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
        ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
        ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2}).ncard :
          ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
        (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3} := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp only [SimpleGraph.mem_externalNeighborSet]
      exact ⟨by decide, 3, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
        ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
        ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3}).ncard :
          ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR

private theorem four_expander :
    (SimpleGraph.completeGraph (Fin 4)).IsCExpander 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro A hA
    rw [card_threshold] at hA
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hAlt : (A.ncard : ℝ) < ((2 : ℕ) : ℝ) := by rw [hcast]; exact hA
    have hAn : A.ncard < 2 := Nat.cast_lt.mp hAlt
    have h01 : A.ncard = 0 ∨ A.ncard = 1 := by omega
    rcases h01 with h0 | h1
    · simp only [h0, Nat.cast_zero, one_mul]
      exact Nat.cast_nonneg _
    · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h1
      have e1 : ((({a} : Set (Fin 4)).ncard : ℝ)) = 1 := by
        simp [Set.ncard_singleton]
      rw [e1, one_mul]
      exact one_le_external_singleton a
  · intro A B hdis hA hB
    rw [card_threshold] at hA hB
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hAcast : ((2 : ℕ) : ℝ) ≤ (A.ncard : ℝ) := by rw [hcast]; exact hA
    have hBcast : ((2 : ℕ) : ℝ) ≤ (B.ncard : ℝ) := by rw [hcast]; exact hB
    have hA2 : 2 ≤ A.ncard := Nat.cast_le.mp hAcast
    have hB2 : 2 ≤ B.ncard := Nat.cast_le.mp hBcast
    have hAne : A.Nonempty := by
      by_contra hcon
      have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
      rw [he, Set.ncard_empty] at hA2
      exact (by decide : ¬ (2 ≤ (0 : ℕ))) hA2
    have hBne : B.Nonempty := by
      by_contra hcon
      have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
      rw [he, Set.ncard_empty] at hB2
      exact (by decide : ¬ (2 ≤ (0 : ℕ))) hB2
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb⟩ := hBne
    have hne : a ≠ b := by
      intro heq
      subst heq
      exact (Set.disjoint_left.mp hdis ha) hb
    exact ⟨a, ha, b, hb, hne⟩

example : 0 < (1 : ℝ) := four_expander.pos

example :
    (1 : ℝ) * ((({0} : Set (Fin 4)).ncard : ℝ)) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :
        ℝ)) := by
  apply four_expander.small_expansion
  rw [card_threshold]
  have e0 : ((({0} : Set (Fin 4)).ncard : ℝ)) = 1 := by
    simp [Set.ncard_singleton]
  rw [e0]
  norm_num

example : ∃ a ∈ ({0, 1} : Set (Fin 4)), ∃ b ∈ ({2, 3} : Set (Fin 4)),
    (SimpleGraph.completeGraph (Fin 4)).Adj a b := by
  apply four_expander.large_edge
  · rw [Set.disjoint_left]
    intro x hx hx2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx2
    rcases hx with rfl | rfl <;> rcases hx2 with h | h <;>
      exact absurd h (by decide)
  · rw [card_threshold]
    have e01 : (({0, 1} : Set (Fin 4)).ncard) = 2 :=
      Set.ncard_pair (by decide)
    rw [e01]
    norm_num
  · rw [card_threshold]
    have e23 : (({2, 3} : Set (Fin 4)).ncard) = 2 :=
      Set.ncard_pair (by decide)
    rw [e23]
    norm_num

example (h : ℝ) (hh : (SimpleGraph.completeGraph (Fin 4)).IsUniformVertexExpander h) :
    0 < h :=
  hh.pos

example (h : ℝ) (hh : (SimpleGraph.completeGraph (Fin 4)).IsUniformVertexExpander h)
    (S : Set (Fin 4)) (hS : (S.ncard : ℝ) ≤ (Nat.card (Fin 4) : ℝ) / 2) :
    h * (S.ncard : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet S).ncard : ℝ)) :=
  hh.small_expansion (SimpleGraph.completeGraph (Fin 4)) S hS

end SimpleGraph.ExpanderTest
