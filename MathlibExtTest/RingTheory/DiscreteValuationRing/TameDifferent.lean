/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.TameDifferent

/-!
# Tests for the tame different-ideal equality

These examples exercise the public API of
`MathlibExt.RingTheory.DiscreteValuationRing.TameDifferent`: the tame
different-ideal equality
`differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast`, under
`map 𝔪A = 𝔪B ^ e` with `IsUnit (e : B)`. This is the correct tame equality,
not the false wild equality in ATLAS N261 lines 1237--1324.
-/

@[expose] public section

open IsLocalRing
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- The tame different-ideal equality applies as stated: under
`map 𝔪A = 𝔪B ^ e` with `IsUnit (e : B)`, the different is `𝔪B ^ (e - 1)`.
This is the tame case only, not the false wild equality in ATLAS. -/
example (e : ℕ) (heUnit : IsUnit (e : B))
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) =
      maximalIdeal B ^ e) :
    differentIdeal A B = maximalIdeal B ^ (e - 1) :=
  differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast A B e heUnit he
