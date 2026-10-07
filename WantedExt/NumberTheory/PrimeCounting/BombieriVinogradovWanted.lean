/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi

/-!
# Bombieri–Vinogradov theorem — wishlist

This file records the classical Bombieri–Vinogradov theorem in its authoritative
von Mangoldt form: the average over moduli of the maximal residue-class error of
the Chebyshev psi function against the inner-variable main term `y / φ(q)`.
-/

@[expose] public section

namespace MetaMathlibExt.NumberTheory.PrimeCounting

/-- The residue-class error of the Chebyshev psi function at level `y` for the
residue `a` modulo `q`, measured against the inner-variable main term
`y / φ(q)`.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, classical theorem display (1.1). -/
public noncomputable def bombieriVinogradovResidueError (y q a : ℕ) : ℝ :=
  |Chebyshev.psiResidueClass (a : ZMod q) (y : ℝ) -
    (y : ℝ) / (Nat.totient q : ℝ)|

open Classical in
/-- The maximal residue-class error at level `y` over the reduced residues
`a < q`, with default zero when there are none.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, inner maximum of display (1.1). -/
public noncomputable def bombieriVinogradovMaxResidueError (y q : ℕ) : ℝ :=
  (((Finset.range q).filter fun a => Nat.Coprime a q).image
    fun a => bombieriVinogradovResidueError y q a).max.unbotD 0

open Classical in
/-- The maximal residue-class error over all levels `y ≤ x` for the modulus
`q`, with default zero.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, maximum over `y ≤ x` in display (1.1). -/
public noncomputable def bombieriVinogradovMaxUpToError (x q : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image
    fun y => bombieriVinogradovMaxResidueError y q).max.unbotD 0

open Classical in
/-- The Bombieri–Vinogradov sum: the previous maximum summed over positive
moduli `q` with `(q : ℝ) ≤ √x / (log x) ^ (A + 5)`. The enumeration over
`Finset.range (x + 1)` is nonbinding for sufficiently large `x`, since the
theorem is eventual.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, outer sum of display (1.1). -/
public noncomputable def bombieriVinogradovSum (x : ℕ) (A : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (x + 1),
    if 0 < q ∧ (q : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 5)
    then bombieriVinogradovMaxUpToError x q else 0

/-- For every `A > 0`, the Bombieri–Vinogradov sum is eventually bounded by
`C * x / (log x) ^ A` for some constant `C > 0`. The main term inside the
maximum is the authoritative inner-variable term `y / φ(q)`, not an
`x`-dependent logarithmic-integral term.

Source: S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets
of Moduli*, arXiv:math/0602116, classical theorem display (1.1), source lines
54–62. The official source bundle has SHA-256
`86b591e2c1c73eadc18774d32318421b8f12a99ab89cc213a3f54aa7953da00f`, the TeX
file has SHA-256
`0826f6d0f8b5f5be49c6238fcdda2bb65d1b1b81a74c964a4328cb5454d0bdb4`, the exact
newline-terminated span has SHA-256
`0c8e89016584b4acbcc9a1c8fd12cb988749e827143e6e83c0e2c4cc025dff0a`, and the
semantic id is `jis_grounded_f3db17ecd03ec2208fa68754`. -/
public theorem_wanted bombieriVinogradov (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ x : ℕ, x₀ ≤ x →
        bombieriVinogradovSum x A ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

end MetaMathlibExt.NumberTheory.PrimeCounting
