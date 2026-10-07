/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DirichletCharacter.QuadraticReciprocityBridge
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

open MetaMathlibExt

example : kroneckerSym 5 (2 * 3) = kroneckerSym 5 2 * kroneckerSym 5 3 :=
  kroneckerSym_mul 5 (by decide) 2 3

example :
    jacobiSym ((7 : ℕ) : ℤ) (5 : ℤ).natAbs = kroneckerSym (5 : ℤ) 7 :=
  jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
    5 7 (by norm_num) (by decide) (by decide) (by decide)

example :
    jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs ≠ kroneckerSym (3 : ℤ) 7 := by
  norm_num [kroneckerSym_prime, kroneckerAtPrime]

#print axioms MetaMathlibExt.kroneckerSym_mul
#print axioms MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
