/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

namespace MetaMathlibExt

public section

/-- One-dimensional `k`-kernel of a sequence.

Source: Adamczewski--Bell, arXiv:1205.4091v1, lines 1105--1129.
The finite-kernel representation: the kernel is the set of all subsequence
maps `n ↦ a (k ^ e * n + r)` as `e : ℕ` varies over exponents and
`r : ℕ` varies over residues with `r < k ^ e`. Each member is hence
recorded as an explicit pair `(e, r)` together with the equality to the
corresponding decimated subsequence. -/
public def kKernel (k : ℕ) {Δ : Type*} (a : ℕ → Δ) : Set (ℕ → Δ) :=
  {b | ∃ e : ℕ, ∃ r : ℕ, r < k ^ e ∧ b = fun n => a (k ^ e * n + r)}

/-- `k`-automaticity of a sequence via the Eilenberg finite-kernel characterization.

Sources: Adamczewski--Bell, arXiv:1205.4091v1, lines 160--195 for the
finite-automaton (DFAO) definition, and lines 1105--1129 for Eilenberg's
equivalence between `k`-automaticity and finiteness of the `k`-kernel.
A sequence is `k`-automatic when `2 ≤ k` and its `k`-kernel `kKernel k a`
is finite. -/
public def IsKAutomatic (k : ℕ) {Δ : Type*} (a : ℕ → Δ) : Prop :=
  2 ≤ k ∧ Finite ↥(kKernel k a)

/-- Christol's theorem: algebraicity iff `p`-automaticity of coefficients.

Source: Adamczewski--Bell, arXiv:1205.4091v1, lines 260--265:
for `q` a positive integral power of the characteristic prime `p`, a series
over `F_q` is algebraic over `F_q(t)` iff its coefficient sequence is
`p`-automatic.

Polynomial-relation interpretation: `IsAlgebraic (Polynomial K) f` asserts a
denominator-cleared nonzero polynomial relation over `K[X]` satisfied by `f`,
which is the formalization of algebraicity over the rational function field
`K(t)`; it is not integrality (`IsIntegral`). The right side is
`p`-automaticity (base `p`, not base `q`) of `fun n => PowerSeries.coeff n f`.
The positivity `0 < r` is preserved verbatim from the source. -/
public theorem_wanted christol_theorem (K : Type*) [Field K] [Finite K] (p q r : ℕ)
    [CharP K p] (hp : Nat.Prime p) (hcard : Nat.card K = q) (hq : q = p ^ r)
    (hr : 0 < r) (f : PowerSeries K) :
    IsAlgebraic (Polynomial K) f ↔ IsKAutomatic p (fun n => PowerSeries.coeff n f)

end

end MetaMathlibExt
