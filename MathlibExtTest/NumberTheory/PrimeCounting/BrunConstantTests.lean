/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.BrunConstant

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

example : brunTwinPrimeReciprocalTerm 0 = 0 := by
  apply brunTwinPrimeReciprocalTerm_eq_zero
  decide

example : brunTwinPrimeReciprocalTerm 3 = (1 : ℝ) / 3 + 1 / 5 := by
  apply brunTwinPrimeReciprocalTerm_eq
  decide

example : brunTwinPrimeReciprocalTerm 5 = (1 : ℝ) / 5 + 1 / 7 := by
  apply brunTwinPrimeReciprocalTerm_eq
  decide

example : HasSum brunTwinPrimeReciprocalTerm brunConstant :=
  hasSum_brunConstant

end MathlibExt.NumberTheory.PrimeCounting
