module

public import Mathlib.Algebra.BigOperators.Fin
public import MathlibExt.Combinatorics.SimpleGraph.CaroWei
import Mathlib.Tactic.NormNum

/-!
# Tests for the Caro–Wei independence bound

Exercises both public declarations on edgeless and complete finite graphs,
plus the empty-vertex boundary case.
-/

/-- Edgeless graph on three vertices: every degree is zero. -/
theorem caroWeiTest_degree_bot (v : Fin 3) :
    (⊥ : SimpleGraph (Fin 3)).degree v = 0 := by
  change ((⊥ : SimpleGraph (Fin 3)).neighborFinset v).card = 0
  rw [SimpleGraph.neighborFinset_bot]
  simp

/-- Complete graph on four vertices: every degree is three. -/
theorem caroWeiTest_degree_top (v : Fin 4) :
    (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by
  change ((⊤ : SimpleGraph (Fin 4)).neighborFinset v).card = 3
  rw [SimpleGraph.neighborFinset_top, Finset.card_compl, Finset.card_singleton,
    Fintype.card_fin]

/-- Reciprocal degree-sum over the edgeless graph on three vertices. -/
theorem caroWeiTest_sum_bot :
    ∑ v : Fin 3, (1 : ℝ) / ((⊥ : SimpleGraph (Fin 3)).degree v + 1) = 3 := by
  have hterm : ∀ v : Fin 3,
      (1 : ℝ) / ((⊥ : SimpleGraph (Fin 3)).degree v + 1) = 1 := by
    intro v
    rw [caroWeiTest_degree_bot v]
    norm_num
  rw [Fin.sum_univ_three]
  simp only [hterm]
  norm_num

/-- Reciprocal degree-sum over the complete graph on four vertices. -/
theorem caroWeiTest_sum_top :
    ∑ v : Fin 4, (1 : ℝ) / ((⊤ : SimpleGraph (Fin 4)).degree v + 1) = 1 := by
  have hterm : ∀ v : Fin 4,
      (1 : ℝ) / ((⊤ : SimpleGraph (Fin 4)).degree v + 1) = 1 / 4 := by
    intro v
    rw [caroWeiTest_degree_top v]
    norm_num
  rw [Fin.sum_univ_four]
  simp only [hterm]
  norm_num

/-- Reciprocal degree-sum over the empty vertex type. -/
theorem caroWeiTest_sum_empty :
    (∑ v : Fin 0, (1 : ℝ) / ((⊥ : SimpleGraph (Fin 0)).degree v + 1)) = 0 := by
  rw [Finset.univ_eq_empty]
  simp

example : (3 : ℝ) ≤ (⊥ : SimpleGraph (Fin 3)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊥ : SimpleGraph (Fin 3)))
  rwa [caroWeiTest_sum_bot] at h

example : (1 : ℝ) ≤ (⊤ : SimpleGraph (Fin 4)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊤ : SimpleGraph (Fin 4)))
  rwa [caroWeiTest_sum_top] at h

example : (0 : ℝ) ≤ (⊥ : SimpleGraph (Fin 0)).indepNum := by
  classical
  have h := SimpleGraph.caroWei_le_indepNum (G := (⊥ : SimpleGraph (Fin 0)))
  rwa [caroWeiTest_sum_empty] at h

example : ∃ s : Finset (Fin 3),
    (⊥ : SimpleGraph (Fin 3)).IsIndepSet (s : Set (Fin 3)) ∧ 3 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊥ : SimpleGraph (Fin 3)))
  rw [caroWeiTest_sum_bot] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩

example : ∃ s : Finset (Fin 4),
    (⊤ : SimpleGraph (Fin 4)).IsIndepSet (s : Set (Fin 4)) ∧ 1 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊤ : SimpleGraph (Fin 4)))
  rw [caroWeiTest_sum_top] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩

example : ∃ s : Finset (Fin 0),
    (⊥ : SimpleGraph (Fin 0)).IsIndepSet (s : Set (Fin 0)) ∧ 0 ≤ s.card := by
  classical
  obtain ⟨s, hs, hsum⟩ :=
    SimpleGraph.exists_isIndepSet_caroWei (G := (⊥ : SimpleGraph (Fin 0)))
  rw [caroWeiTest_sum_empty] at hsum
  exact ⟨s, hs, by exact_mod_cast hsum⟩
