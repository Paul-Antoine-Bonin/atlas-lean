/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.Chebyshev
import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi

example {q : ℕ} (a : ZMod q) : Chebyshev.psiResidueClass a 0 = 0 := by
  exact Chebyshev.psiResidueClass_of_lt_one a zero_lt_one

example {q : ℕ} (a : ZMod q) : Chebyshev.psiResidueClass a (-3) = 0 := by
  exact Chebyshev.psiResidueClass_of_lt_one a (by norm_num)

example (x : ℝ) : Chebyshev.psiResidueClass (0 : ZMod 1) x = Chebyshev.psi x := by
  unfold Chebyshev.psiResidueClass Chebyshev.psi
    ArithmeticFunction.vonMangoldt.residueClass
  apply Finset.sum_congr rfl
  intro n _
  rw [Set.indicator_of_mem]
  exact Subsingleton.elim _ _
