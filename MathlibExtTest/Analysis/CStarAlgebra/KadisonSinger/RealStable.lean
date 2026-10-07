/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.RealStable

open scoped ComplexOrder

open MvPolynomial

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable

private lemma finOne_one_posSemidef :
    (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := by
  rw [show (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.diagonal (fun _ ↦ 1) by
    ext i j
    fin_cases i
    fin_cases j
    simp]
  exact Matrix.PosSemidef.diagonal (fun i ↦ by norm_num)

-- The determinant polynomial of a positive one-dimensional matrix is stable.
example :
    (mixedDetPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsStable := by
  apply mixedDetPolynomial_isStable_of_posSemidef
  intro i
  exact finOne_one_posSemidef

-- The same concrete determinant polynomial is real stable.
example :
    (mixedDetPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsRealStable := by
  apply mixedDetPolynomial_isRealStable_of_posSemidef
  intro i
  exact finOne_one_posSemidef

-- A concrete mixed characteristic polynomial is monic.
example :
    (mixedCharacteristicPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).Monic :=
  mixedCharacteristicPolynomial_monic _

-- Its degree is the dimension of the one-dimensional matrix space.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).natDegree = 1 := by
  simpa using mixedCharacteristicPolynomial_natDegree
    (fun _ : Fin 1 ↦ !![(1 : ℂ)])

-- Positive semidefiniteness makes the concrete mixed characteristic polynomial real-rooted.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsRealRooted := by
  apply mixedCharacteristicPolynomial_isRealRooted_of_posSemidef
  intro i
  exact finOne_one_posSemidef

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable
