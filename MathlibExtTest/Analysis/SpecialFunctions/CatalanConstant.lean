/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.CatalanConstant

example : Real.catalanConstant =
    ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 :=
  Real.catalanConstant_eq_tsum

example : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
    Real.catalanConstant :=
  Real.hasSum_catalanConstant

#print axioms Real.catalanConstant
