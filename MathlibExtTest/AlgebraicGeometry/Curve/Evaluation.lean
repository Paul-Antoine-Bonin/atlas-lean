/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.Evaluation

@[expose] public section

namespace CurveDivisor

variable {C G : Type*} [CommGroup G]

example (f : C → G) (D : CurveDivisor C) :
    eval f D = D.prod (fun P n ↦ f P ^ n) :=
  eval_eq_prod f D

example (f : C → G) : eval f (0 : CurveDivisor C) = 1 := by
  simp

example (f : C → G) (P : C) (n : ℤ) :
    eval f (Finsupp.single P n) = f P ^ n :=
  eval_single f P n

example (f : C → G) (D₁ D₂ : CurveDivisor C) :
    eval f (D₁ + D₂) = eval f D₁ * eval f D₂ :=
  eval_add f D₁ D₂

example (f : C → G) (n : ℤ) (D : CurveDivisor C) :
    eval f (n • D) = eval f D ^ n :=
  eval_zsmul f n D

example (f : C → G) (P : C) :
    eval f (Finsupp.single P (2 : ℤ)) = f P ^ (2 : ℤ) :=
  eval_single f P 2

example (f : C → G) (P : C) :
    eval f (Finsupp.single P (-1 : ℤ)) = (f P)⁻¹ := by
  rw [eval_single, zpow_neg_one]

end CurveDivisor
