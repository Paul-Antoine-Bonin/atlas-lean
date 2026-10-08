/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EllipticCurve.GaloisRepresentation
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

@[expose] public section

/-!
# Determinant of the mod-`p` Galois representation (source statement)

Gonzalez-Jimenez–Lozano-Robledo, *Elliptic Curves with abelian division fields*,
arXiv:1511.08578v2, Math. Z. 283 (2016), DOI `10.1007/s00209-016-1623-z`.
Frozen source SHA-256 `33306eccf5fce60cc116e22c4227a9125a35370982c51473be94db57ef21abc9`.

The source fixes an elliptic curve over `ℚ`, a prime `p > 2`, and the natural Galois
action `ρ_{E,p}` on `E[p]`; its proof of Proposition `prop-borel2` uses that the
determinant of `ρ_{E,p}` equals the mod-`p` cyclotomic character. The infrastructure
(`galDetHom`) lives in the production module; the identity itself is stated here because
Mathlib lacks the Weil pairing and the rank-two torsion theorem. The cardinality
hypothesis of `modularCyclotomicCharacter` is discharged by an explicit primitive root.
-/

namespace MetaMathlibExt

open WeierstrassCurve

theorem_wanted cyclotomicDeterminant (W : Affine ℚ) [W.IsElliptic] (p : ℕ)
    [Fact p.Prime] (hp : 2 < p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (σ : Field.absoluteGaloisGroup ℚ) :
    galDetHom W p σ =
      modularCyclotomicCharacter (AlgebraicClosure ℚ) hζ.card_rootsOfUnity
        (galAlgEquiv σ).toRingEquiv

end MetaMathlibExt
