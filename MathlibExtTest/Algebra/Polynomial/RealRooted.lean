/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RealRooted

@[expose] public section

open scoped ComplexOrder

namespace MathlibExtTest.Algebra.Polynomial.RealRooted

noncomputable section

/-- A linear polynomial used to exercise the real-rooted API. -/
def linearPolynomial (a : ℝ) : Polynomial ℂ :=
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

-- The real affine polynomial `X - 2` satisfies the conjugate-root criterion.
example : (Polynomial.X - Polynomial.C (2 : ℂ)).IsRealRooted := by
  apply Polynomial.isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
  · exact (Polynomial.monic_X_sub_C 2).ne_zero
  · have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    simp [htwo]
  · intro z hz
    rw [Polynomial.roots_X_sub_C] at hz
    have hz' : z = 2 := by simpa using hz
    rw [hz']
    norm_num

-- The unique root of `X - 2` lies below its largest real root.
example :
    ((2 : ℂ).re) ≤ (linearPolynomial 2).maxRealRoot := by
  apply Polynomial.root_re_le_maxRealRoot
  simp [linearPolynomial, Polynomial.roots_X_sub_C]

-- A nonconstant affine polynomial has a root attaining its largest real part.
example :
    ∃ z ∈ (linearPolynomial 2).roots,
      z.re = (linearPolynomial 2).maxRealRoot := by
  apply Polynomial.exists_root_re_eq_maxRealRoot
  apply Polynomial.roots_ne_zero_of_natDegree_pos
  rw [linearPolynomial_natDegree]
  norm_num

-- Positive degree forces the affine polynomial's root multiset to be nonempty.
example : (linearPolynomial 2).roots ≠ 0 := by
  apply Polynomial.roots_ne_zero_of_natDegree_pos
  rw [linearPolynomial_natDegree]
  norm_num

-- For `X - 2`, the largest real root is itself a member of the roots.
example :
    ((linearPolynomial 2).maxRealRoot : ℂ) ∈ (linearPolynomial 2).roots := by
  apply Polynomial.coe_maxRealRoot_mem_roots (linearPolynomial_realRooted 2)
  rw [linearPolynomial_natDegree]
  norm_num

-- The monic affine polynomial is positive to the right of its largest root.
example : 0 < ((linearPolynomial 2).eval (3 : ℂ)).re := by
  apply Polynomial.eval_re_pos_of_maxRealRoot_lt
      (linearPolynomial_monic 2) (linearPolynomial_realRooted 2)
  rw [linearPolynomial_maxRealRoot]
  norm_num

-- It is nonnegative at its largest root.
example : 0 ≤ ((linearPolynomial 2).eval (2 : ℂ)).re := by
  apply Polynomial.eval_re_nonneg_of_maxRealRoot_le
      (x := (2 : ℝ)) (linearPolynomial_monic 2) (linearPolynomial_realRooted 2)
  rw [linearPolynomial_maxRealRoot]

end

end MathlibExtTest.Algebra.Polynomial.RealRooted
