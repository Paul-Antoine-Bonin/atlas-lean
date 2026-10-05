import MathlibExt.Analysis.CStarAlgebra.KadisonSinger

open scoped Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

noncomputable section

private def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

private lemma pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

private lemma pauliX_diagonal (i : Fin 2) : pauliX i i = 0 := by
  fin_cases i <;> rfl

private lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliX_norm_le_one : ‖pauliX‖ ≤ 1 := by
  have hstar : star pauliX = pauliX := pauliX_isHermitian
  have hsquare : ‖pauliX‖ * ‖pauliX‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hstar, pauliX_mul_self, norm_one]
  nlinarith [norm_nonneg pauliX]

-- The theorem gives a half-norm paving of the nonzero two-dimensional Pauli matrix.
example :
    ∃ (r : ℕ), 0 < r ∧ ∃ c : Fin 2 → Fin r, ∀ j,
      ‖pavingProj 2 r c j * pauliX * pavingProj 2 r c j‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨r, hr, hall⟩ := kadison_singer_paving (1 / 2) (by norm_num)
  obtain ⟨c, hc⟩ := hall 2 pauliX pauliX_isHermitian pauliX_diagonal
    pauliX_norm_le_one
  exact ⟨r, hr, c, hc⟩

end

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
