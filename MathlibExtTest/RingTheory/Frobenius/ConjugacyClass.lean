/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Frobenius.ConjugacyClass

/-!
# Regression examples for the Frobenius conjugacy-class API

These examples exercise the root-level declarations `arithFrobConjClass`,
`arithFrobConjClass_mem_carrier`, and `arithFrobConjClass_eq_of_under_eq`
through the public import surface, as a downstream user would see them.
-/

@[expose] public section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]

-- The class unfolds to the quotient projection of the chosen Frobenius element.
example (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] :
    arithFrobConjClass (R := R) (G := G) Q =
      ConjClasses.mk (arithFrobAt R G Q) :=
  rfl

-- The chosen Frobenius element lies in its conjugacy class.
example (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] :
    arithFrobAt R G Q ∈ (arithFrobConjClass (R := R) (G := G) Q).carrier :=
  arithFrobConjClass_mem_carrier Q

-- Primes lying over the same prime of `R` share their Frobenius class.
example (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q]
    [Q'.IsPrime] [Finite (S ⧸ Q')] [Algebra.IsUnramifiedAt R Q']
    (h : Q.under R = Q'.under R) :
    arithFrobConjClass (R := R) (G := G) Q =
      arithFrobConjClass (R := R) (G := G) Q' :=
  arithFrobConjClass_eq_of_under_eq Q Q' h

-- Membership transfers across equal contractions via the class equality.
example (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q]
    [Q'.IsPrime] [Finite (S ⧸ Q')] [Algebra.IsUnramifiedAt R Q']
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q ∈ (arithFrobConjClass (R := R) (G := G) Q').carrier := by
  rw [← arithFrobConjClass_eq_of_under_eq Q Q' h]
  exact arithFrobConjClass_mem_carrier Q
