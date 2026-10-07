/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.IntegralClosureComplete

@[expose] public section

namespace MathlibExtTest.RingTheory.DiscreteValuationRing.IntegralClosureComplete

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra A B] [Algebra.IsIntegral A B]
variable (p : Ideal A) [p.IsMaximal] [IsAdicComplete p A]
variable (Q : Ideal B) [Q.IsMaximal]

example : Q.comap (algebraMap A B) = p :=
  Ideal.comap_eq_base_maximal_of_isAdicComplete_of_isIntegral p Q

variable [IsDomain A] [IsDomain B]

example : IsLocalRing B :=
  isLocalRing_of_isIntegral_of_isAdicComplete_maximal p

section Tower

variable (R K L S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing S] [IsDomain S] [Algebra R S] [Algebra S L]
  [IsScalarTower R S L] [IsIntegralClosure S R L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

example : IsLocalRing S :=
  IsIntegralClosure.isLocalRing_of_isAdicComplete R K L S

example : IsDiscreteValuationRing S :=
  IsIntegralClosure.isDiscreteValuationRing_of_isAdicComplete R K L S

example : ∃! Q : Ideal S, Q ∈ (IsLocalRing.maximalIdeal R).primesOver S :=
  IsIntegralClosure.existsUnique_primesOver_maximalIdeal_of_isAdicComplete R K L S

example [IsLocalRing S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
  IsIntegralClosure.isAdicComplete_of_isAdicComplete (A := R) (K := K) (L := L)
    (B := S)

example [IsLocalRing S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  let := IsIntegralClosure.isAdicComplete_of_isAdicComplete (A := R) (K := K)
    (L := L) (B := S)
  exact inferInstance

end Tower

section ValuationIntegers

variable (R K L Gamma : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [LinearOrderedCommGroupWithZero Gamma] (v : Valuation L Gamma)
  [Algebra R ↥v.integer]
  [IsScalarTower R ↥v.integer L]
  [IsLocalHom (algebraMap R ↥v.integer)]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

example : IsIntegralClosure ↥v.integer R L :=
  Valuation.integer_isIntegralClosure_of_isAdicComplete R K L Gamma v

example : Module.Finite R ↥v.integer :=
  Valuation.module_finite_integer_of_isAdicComplete R K L Gamma v

end ValuationIntegers

end MathlibExtTest.RingTheory.DiscreteValuationRing.IntegralClosureComplete
