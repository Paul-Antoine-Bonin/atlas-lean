/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GenocchiNumber
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExtTest

example : MetaMathlibExt.genocchiPowerSeries
    = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ :=
  rfl

example (n : ℕ) : MetaMathlibExt.genocchiNumber n
    = (n.factorial : ℚ) * (PowerSeries.coeff n) MetaMathlibExt.genocchiPowerSeries :=
  MetaMathlibExt.genocchiNumber_eq n

private lemma invExpAddOne_coeff_zero :
    PowerSeries.coeff 0 ((PowerSeries.exp ℚ + 1)⁻¹) = 1 / 2 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv]
  norm_num

private lemma invExpAddOne_coeff_one :
    PowerSeries.coeff 1 ((PowerSeries.exp ℚ + 1)⁻¹) = -1 / 4 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero]

private lemma invExpAddOne_coeff_two :
    PowerSeries.coeff 2 ((PowerSeries.exp ℚ + 1)⁻¹) = 0 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero, invExpAddOne_coeff_one]

private lemma invExpAddOne_coeff_three :
    PowerSeries.coeff 3 ((PowerSeries.exp ℚ + 1)⁻¹) = 1 / 48 := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, invExpAddOne_coeff_zero, invExpAddOne_coeff_one,
    invExpAddOne_coeff_two, Nat.factorial]

example : MetaMathlibExt.genocchiNumber 0 = 0 := by
  simp [MetaMathlibExt.genocchiNumber, MetaMathlibExt.genocchiPowerSeries]

example : MetaMathlibExt.genocchiNumber 1 = 1 := by
  change (1 : ℚ) * PowerSeries.coeff 1
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = 1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_zero]
  norm_num

example : MetaMathlibExt.genocchiNumber 2 = -1 := by
  change (2 : ℚ) * PowerSeries.coeff 2
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = -1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_one]
  norm_num

example : MetaMathlibExt.genocchiNumber 4 = 1 := by
  change (24 : ℚ) * PowerSeries.coeff 4
    (PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹) = 1
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    invExpAddOne_coeff_three]
  norm_num

end MetaMathlibExtTest
