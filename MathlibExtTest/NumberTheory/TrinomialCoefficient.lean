/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

example : trinomialCoefficient 0 0 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_one]

example : trinomialCoefficient 0 1 = 0 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_one]

example : trinomialCoefficient 1 0 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 1 1 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 1 2 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 2 2 = 3 := by
  change ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2).coeff 2 = 3
  ring_nf
  norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

example : trinomialCoefficient 2 5 = 0 := by
  change ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2).coeff 5 = 0
  ring_nf
  norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

#print axioms MetaMathlibExt.trinomialCoefficient

end MetaMathlibExt

end
