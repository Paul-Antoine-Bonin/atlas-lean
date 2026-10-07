/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Localization.RegularAt

@[expose] public section

example (ev : ℤ →+* ℚ) (a : ℤ) :
    FractionRing.IsRegularAt ev (algebraMap ℤ (FractionRing ℤ) a) :=
  FractionRing.isRegularAt_algebraMap ev a

example (ev : ℤ →+* ℚ) : FractionRing.IsRegularAt ev (0 : FractionRing ℤ) :=
  FractionRing.isRegularAt_zero ev

example (ev : ℤ →+* ℚ) : FractionRing.IsRegularAt ev (1 : FractionRing ℤ) :=
  FractionRing.isRegularAt_one ev

example (X : Set (Fin 1 → ℚ)) (P : X) (p : MvPolynomial (Fin 1) ℚ) :
    MvPolynomial.AffineCoordinateRing.evalAt X P
        (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal ℚ X) p) =
      MvPolynomial.aeval (P : Fin 1 → ℚ) p := by
  simp

variable (X : Set (Fin 1 → ℚ))
  [IsDomain (MvPolynomial.AffineCoordinateRing X)] (P : X)

example (a : MvPolynomial.AffineCoordinateRing X) :
    MvPolynomial.AffineCoordinateRing.IsRegularAt X
      (algebraMap _ (FractionRing (MvPolynomial.AffineCoordinateRing X)) a) P :=
  MvPolynomial.AffineCoordinateRing.isRegularAt_algebraMap X a P
