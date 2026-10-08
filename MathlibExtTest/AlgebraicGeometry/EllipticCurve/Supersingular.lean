/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.Supersingular

attribute [local instance] Classical.decEq

namespace WeierstrassCurve.Affine

#check (IsSupersingular :
  ∀ {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic], Prop)

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : W.IsSupersingular) {r : ℕ} (hr : 0 < r) {P : W.Point}
    (hP : (p ^ r) • P = 0) : P = 0 :=
  h.pow_torsion W hr hP

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : ∀ r : ℕ, 0 < r → ∀ P : W.Point, (p ^ r) • P = 0 → P = 0) :
    W.IsSupersingular :=
  IsSupersingular.of_pow_torsion W h

example {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (h : W.IsSupersingular) (P : W.Point) (hP : p • P = 0) : P = 0 :=
  h P hP

end WeierstrassCurve.Affine
