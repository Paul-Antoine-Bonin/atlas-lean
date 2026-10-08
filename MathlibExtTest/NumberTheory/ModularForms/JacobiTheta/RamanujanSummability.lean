/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability

namespace MetaMathlibExt

example (a b : ℂ) (h : ‖a * b‖ < 1) :
    Summable (fun n : ℤ => ‖ramanujanThetaTerm a b n‖) :=
  ramanujanTheta_summable a b h

example : Summable (fun n : ℤ => ‖ramanujanThetaTerm (0 : ℂ) (0 : ℂ) n‖) :=
  ramanujanTheta_summable _ _ (by simp)

#print axioms MetaMathlibExt.ramanujanTheta_summable

end MetaMathlibExt
