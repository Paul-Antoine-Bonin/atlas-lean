/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

-- Mertens' theorem in arithmetic progressions, applied to the reduced
-- residue class `1` modulo `4`: the von Mangoldt reciprocal sum over the
-- class differs from `log x / φ(4)` by a bounded error.
example : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
      Real.log x / ((4).totient : ℝ)| ≤ C :=
  Chebyshev.exists_abs_sum_residueClass_div_sub_log_le (1 : ZMod 4) isUnit_one
