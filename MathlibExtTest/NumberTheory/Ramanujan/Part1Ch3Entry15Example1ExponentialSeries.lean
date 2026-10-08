/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry15Example1ExponentialSeries

open scoped BigOperators

open MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15Example1ExponentialSeries

-- The theorem specializes to the ordinary binomial series when `n = 1`.
example (m : ℝ) :
    HasSum (fun k : ℕ =>
      if k = 0 then (1 : ℝ)
      else (m * ∏ j ∈ Finset.range (k - 1), (m + (k : ℝ) - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ (k : ℝ) * (Nat.factorial k : ℝ))) ((2 : ℝ) ^ m) := by
  simpa using ramanujan_part1_ch3_entry15_example1_exponential_series m 1 (by norm_num)
    (by norm_num)
