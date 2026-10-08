/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.Barrier

open scoped BigOperators ComplexOrder

open MvPolynomial

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Barrier

private lemma finOne_one_posSemidef :
    (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := by
  rw [show (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.diagonal (fun _ ↦ 1) by
    ext i j
    fin_cases i
    fin_cases j
    simp]
  exact Matrix.PosSemidef.diagonal (fun i ↦ by norm_num)

-- The barrier bound applies to the one-dimensional identity covariance matrix.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).maxRealRoot ≤
        (1 + Real.sqrt 1) ^ 2 := by
  apply mixedCharacteristicPolynomial_maxRealRoot_le
  · norm_num
  · intro i
    exact finOne_one_posSemidef
  · ext i j
    fin_cases i
    fin_cases j
    simp
  · intro i
    simp [Matrix.trace]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Barrier
