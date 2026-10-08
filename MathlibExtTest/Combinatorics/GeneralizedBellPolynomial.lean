/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.GeneralizedBellPolynomial
import Mathlib.Algebra.Ring.Int.Defs

open MetaMathlibExt

example : genStirling (0 : ℤ) (1 : ℤ) 0 0 = 1 := by decide
example : genStirling (0 : ℤ) (1 : ℤ) 0 5 = 0 := by decide
example : genStirling (0 : ℤ) (1 : ℤ) 3 0 = 0 := by decide

example : genStirling (2 : ℤ) (3 : ℤ) 2 1 = 3 := by decide
example : genStirling (2 : ℤ) (3 : ℤ) 2 5 = 0 := by decide

example : genBellNumber (0 : ℤ) (1 : ℤ) 1 = 1 := by decide
example : genBellNumber (0 : ℤ) (1 : ℤ) 2 = 2 := by decide

example : genBellPolynomial (0 : ℤ) (1 : ℤ) 2 5 = 30 := by decide
example : genBellPolynomial (0 : ℤ) (1 : ℤ) 2 (-1) = 0 := by decide
example : genBellPolynomial (0 : ℤ) (1 : ℤ) 3 2 = 22 := by decide
example : genBellPolynomial (0 : ℤ) (1 : ℤ) 3 (-1) = 1 := by decide

example : genBellPolynomial (2 : ℤ) (3 : ℤ) 2 2 = 10 := by decide
example : genBellPolynomial (2 : ℤ) (3 : ℤ) 2 5 = 40 := by decide
example : genBellPolynomial (2 : ℤ) (3 : ℤ) 3 2 = 98 := by decide
example : genBellNumber (2 : ℤ) (3 : ℤ) 3 = 37 := by decide

example : genBellPolynomial (2 : ℤ) (3 : ℤ) 3 1 = genBellNumber (2 : ℤ) (3 : ℤ) 3 :=
  genBellPolynomial_eval_one _ _ _
