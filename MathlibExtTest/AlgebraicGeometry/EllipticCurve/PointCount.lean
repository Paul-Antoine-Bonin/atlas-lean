/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount

namespace WeierstrassCurve.Affine.PointCountTest

open WeierstrassCurve

universe u

example {R : Type u} [CommRing R] [Finite R] (W : Affine R) : Finite W.Point :=
  inferInstance

variable {F : Type u} [Field F] [Finite F] (W : Affine F) [W.IsElliptic]

example : W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
  W.frobeniusTrace_eq

example : Nat.card W.Point = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 :=
  W.natCard_point_eq_natCard_affineSolutions_add_one

example : Nat.card W.Point ≤ 2 * Nat.card F + 1 :=
  W.natCard_point_le_two_mul_natCard_add_one

example : (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace :=
  W.natCard_point_eq_natCard_add_one_sub_frobeniusTrace

example : (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 :=
  W.natCard_point_add_frobeniusTrace_eq

end WeierstrassCurve.Affine.PointCountTest

namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The curve `y² = x³ + 1` over `ZMod 5`. -/
private def curve : WeierstrassCurve.Affine (ZMod 5) :=
  ⟨0, 0, 0, 0, 1⟩

private instance : curve.IsShortNF := ⟨rfl, rfl, rfl⟩

private instance : curve.IsElliptic :=
  WeierstrassCurve.IsElliptic.mk (by
    rw [curve.Δ_of_isShortNF]
    apply isUnit_iff_ne_zero.mpr
    have h : (16 : ZMod 5) ≠ 0 ∧ (27 : ZMod 5) ≠ 0 := ⟨by decide, by decide⟩
    simpa [curve] using h)

private abbrev AffineSolution :=
  {xy : ZMod 5 × ZMod 5 // xy.2 ^ 2 = xy.1 ^ 3 + 1}

private instance : Fintype AffineSolution :=
  Fintype.subtype (Finset.univ.filter fun xy : ZMod 5 × ZMod 5 => xy.2 ^ 2 = xy.1 ^ 3 + 1)
    (by simp)

private lemma equation_iff (xy : ZMod 5 × ZMod 5) :
    curve.Equation xy.1 xy.2 ↔ xy.2 ^ 2 = xy.1 ^ 3 + 1 := by
  rw [WeierstrassCurve.Affine.Equation, curve.evalEval_polynomial]
  simp [curve, sub_eq_zero]

example : Fintype.card AffineSolution = 5 := by
  decide

private lemma natCard_affineSolutions :
    Nat.card {xy : ZMod 5 × ZMod 5 // curve.Equation xy.1 xy.2} = 5 := by
  rw [Nat.card_congr (Equiv.subtypeEquivProp (funext fun xy => propext (equation_iff xy))),
    Nat.card_eq_fintype_card]
  decide

example : Nat.card curve.Point = 6 := by
  rw [curve.natCard_point_eq_natCard_affineSolutions_add_one, natCard_affineSolutions]

example : Nat.card curve.Point ≤ 11 := by
  simpa using curve.natCard_point_le_two_mul_natCard_add_one

example : curve.frobeniusTrace = 0 := by
  rw [curve.frobeniusTrace_eq]
  norm_num [show Nat.card curve.Point = 6 by
    rw [curve.natCard_point_eq_natCard_affineSolutions_add_one, natCard_affineSolutions]]

end WeierstrassCurve.Affine.PointCountTest.ZModFive
