import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.Paving

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

noncomputable section

universe v

-- Frame partitions accept frame indices in an independent universe.
example (hMSS : FiniteMSSBound.{0}) {I : Type v} [Fintype I] {d r : ℕ}
    (hr : 0 < r) (frame : I → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (frame i) (star (frame i)) = 1)
    (hframeNorm : ∀ i, ∑ k, ‖frame i k‖ ^ 2 ≤ δ) :
    ∃ c : I → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (frame i) (star (frame i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 :=
  exists_frame_partition_of_finiteMSS hMSS hr frame δ hδ hframe hframeNorm

private def unitFrame : Fin 1 → Fin 1 → ℂ := fun _ _ ↦ 1

private lemma unitFrame_sum :
    ∑ i, Matrix.vecMulVec (unitFrame i) (star (unitFrame i)) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [unitFrame, Matrix.vecMulVec_apply, Pi.star_apply]

private lemma unitFrame_norm (i : Fin 1) :
    ∑ k, ‖unitFrame i k‖ ^ 2 ≤ (1 : ℝ) := by
  simp [unitFrame]

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

-- Anderson paving specializes the universe-polymorphic MSS bound to its `Fin` indices.
example (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 :=
  andersonPaving_of_finiteMSS hMSS hr A hA hdiagA hnormA

-- The MSS bound partitions a concrete one-vector Parseval frame into two colours.
example (hMSS : FiniteMSSBound.{0}) :
    ∃ c : Fin 1 → Fin 2, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (unitFrame i) (star (unitFrame i))) :
          Matrix (Fin 1) (Fin 1) ℂ)‖ ≤
        (1 / Real.sqrt 2 + Real.sqrt 1) ^ 2 := by
  apply exists_frame_partition_of_finiteMSS hMSS (r := 2) (d := 1)
  · norm_num
  · norm_num
  · exact unitFrame_sum
  · exact unitFrame_norm

-- The finite MSS bound paves the nonzero Pauli matrix at two base colours.
example (hMSS : FiniteMSSBound.{0}) :
    ∃ c : Fin 2 → Fin (2 * 2), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * pauliX *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt 2 + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  exact andersonPaving_of_finiteMSS hMSS (r := 2) (by norm_num) pauliX
    pauliX_isHermitian pauliX_diagonal pauliX_norm_le_one

end

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
