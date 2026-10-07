/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.RegularizedIntegral

open MeasureTheory Set

example :
    (Real.eulerMascheroniConstant : ℂ) =
      (∫ t : ℝ in 0..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ)) -
        ∫ t : ℝ in Ioi 1, ((Real.exp (-t) / t : ℝ) : ℂ) :=
  Real.eulerMascheroniConstant_eq_regularized_integrals
