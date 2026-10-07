/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpectralNormUnitBall
import Mathlib.Tactic

namespace MetaMathlibExt

@[expose] public section

open Polynomial

-- Focused examples applying both directions of each public theorem.
-- These assume the essential base-unit-ball hypothesis `hA` as an explicit premise.

variable {A K L B : Type*} [CommRing A] [IsDomain A]
  [NontriviallyNormedField K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L]
  [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]

example (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L)
    (h : spectralNorm K L x ≤ 1) : IsIntegral A x :=
  (spectralNorm_le_one_iff_isIntegral hA x).mp h

example (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L)
    (h : IsIntegral A x) : spectralNorm K L x ≤ 1 :=
  (spectralNorm_le_one_iff_isIntegral hA x).mpr h

example (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L)
    (h : spectralNorm K L x ≤ 1) : ∃ b : B, algebraMap B L b = x :=
  (spectralNorm_le_one_iff_exists_integralClosure hA x).mp h

example (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L)
    (h : ∃ b : B, algebraMap B L b = x) : spectralNorm K L x ≤ 1 :=
  (spectralNorm_le_one_iff_exists_integralClosure hA x).mpr h

end

end MetaMathlibExt
