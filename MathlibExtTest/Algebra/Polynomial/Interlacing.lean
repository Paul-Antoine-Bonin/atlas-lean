/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Polynomial.Interlacing

open scoped BigOperators ComplexOrder

namespace MathlibExtTest.Algebra.Polynomial.Interlacing

noncomputable section

private def linearPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.X - Polynomial.C (a : ℂ)

private lemma linearPolynomial_monic (a : ℝ) : (linearPolynomial a).Monic :=
  Polynomial.monic_X_sub_C _

private lemma linearPolynomial_natDegree (a : ℝ) :
    (linearPolynomial a).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C _

private lemma linearPolynomial_realRooted (a : ℝ) :
    (linearPolynomial a).IsRealRooted := by
  intro z hz
  rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
  have hz' : z = (a : ℂ) := by simpa using hz
  rw [hz']
  simp

private lemma linearPolynomial_maxRealRoot (a : ℝ) :
    (linearPolynomial a).maxRealRoot = a := by
  rw [linearPolynomial, Polynomial.maxRealRoot, Polynomial.roots_X_sub_C]
  simp

private def weights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private def family : Fin 2 → Polynomial ℂ :=
  ![linearPolynomial 1, linearPolynomial 2]

private lemma weightedSum_eq :
    ∑ i, (weights i : ℂ) • family i = linearPolynomial (3 / 2) := by
  ext n
  by_cases hzero : n = 0
  · subst n
    norm_num [weights, family, linearPolynomial, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_one]
  · by_cases hone : n = 1
    · subst n
      norm_num [weights, family, linearPolynomial, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_one]
    · simp [weights, family, linearPolynomial, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_one, hzero, Ne.symm hone]

private lemma linearCombination_eq (a b t : ℝ) :
    (1 - (t : ℂ)) • linearPolynomial a + (t : ℂ) • linearPolynomial b =
      linearPolynomial ((1 - t) * a + t * b) := by
  simp [linearPolynomial, Polynomial.smul_eq_C_mul]
  ring

private lemma family_upperInterlacing (i : Fin 2) :
    (family i).HasUpperInterlacingPoint 0 := by
  fin_cases i
  · change (linearPolynomial 1).HasUpperInterlacingPoint 0
    constructor
    · rw [linearPolynomial_maxRealRoot]
      norm_num
    · intro z hz
      rw [linearPolynomial_maxRealRoot] at hz
      rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
      simp at hz
  · change (linearPolynomial 2).HasUpperInterlacingPoint 0
    constructor
    · rw [linearPolynomial_maxRealRoot]
      norm_num
    · intro z hz
      rw [linearPolynomial_maxRealRoot] at hz
      rw [linearPolynomial, Polynomial.roots_X_sub_C] at hz
      simp at hz

-- Between an upper interlacing point and the largest root, its value is nonpositive.
example : ((linearPolynomial 2).eval ((3 / 2 : ℝ) : ℂ)).re ≤ 0 := by
  apply Polynomial.eval_re_nonpos_of_upperInterlacing
      (linearPolynomial_monic 2) (linearPolynomial_realRooted 2)
      (a := 0) (x := 3 / 2)
  · simpa [family] using family_upperInterlacing 1
  · norm_num
  · rw [linearPolynomial_maxRealRoot]
    norm_num
  · rw [linearPolynomial_natDegree]
    norm_num

-- A two-polynomial family with a common interlacing point selects a bounded member.
example :
    ∃ i, (family i).maxRealRoot ≤
      (∑ j, (weights j : ℂ) • family j).maxRealRoot := by
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing
  · intro i
    fin_cases i <;> norm_num [weights]
  · intro i
    fin_cases i <;> exact linearPolynomial_monic _
  · intro i
    fin_cases i <;> exact linearPolynomial_realRooted _
  · intro i
    fin_cases i <;> simp [family, linearPolynomial_natDegree]
  · exact ⟨0, family_upperInterlacing⟩
  · rw [weightedSum_eq]
    exact linearPolynomial_monic _
  · rw [weightedSum_eq]
    exact linearPolynomial_realRooted _

-- Real-rootedness of every segment also selects a bounded family member.
example :
    ∃ i, (family i).maxRealRoot ≤
      (∑ j, (weights j : ℂ) • family j).maxRealRoot := by
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_segment_realRooted
      (hne := inferInstance) (n := 1)
  · norm_num
  · intro i
    fin_cases i <;> norm_num [weights]
  · intro i
    fin_cases i <;>
      exact ⟨linearPolynomial_natDegree _, linearPolynomial_monic _⟩
  · rw [weightedSum_eq]
    exact ⟨linearPolynomial_natDegree _, linearPolynomial_monic _⟩
  · intro i t ht
    rw [weightedSum_eq]
    fin_cases i
    · change ((1 - (t : ℂ)) • linearPolynomial (3 / 2) +
          (t : ℂ) • linearPolynomial 1).IsRealRooted
      rw [linearCombination_eq]
      exact linearPolynomial_realRooted _
    · change ((1 - (t : ℂ)) • linearPolynomial (3 / 2) +
          (t : ℂ) • linearPolynomial 2).IsRealRooted
      rw [linearCombination_eq]
      exact linearPolynomial_realRooted _

end

end MathlibExtTest.Algebra.Polynomial.Interlacing
