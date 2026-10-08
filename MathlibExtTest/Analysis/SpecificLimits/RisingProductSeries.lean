/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.RisingProductSeries

example (x : ℂ) :
    Summable (fun j : ℕ =>
      (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (0 + 1 * ((r + 1 : ℕ) : ℂ))) :=
  Complex.summable_neg_pow_mul_pow_div_prod_add_mul x fun r => by simp [Nat.cast_add_one_ne_zero]

example {b c : ℂ} (hc : ∀ r : ℕ, c + b * ((r + 1 : ℕ) : ℂ) ≠ 0) :
    Summable (fun j : ℕ =>
      (-b) ^ j * 0 ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (c + b * ((r + 1 : ℕ) : ℂ))) :=
  Complex.summable_neg_pow_mul_pow_div_prod_add_mul 0 hc

example (x : ℂ) :
    Summable (fun j : ℕ =>
      (-0 : ℂ) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (1 + 0 * ((r + 1 : ℕ) : ℂ))) :=
  Complex.summable_neg_pow_mul_pow_div_prod_add_mul x fun r => by simp
