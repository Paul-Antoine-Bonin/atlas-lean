/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tu-Deng conjecture
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.DigitalBinomialTheorem
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.TuDengConjectureWanted

open MetaMathlibExt (binDigitSum)

def tuDengConjecture : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ t : ZMod (2 ^ k - 1), t ≠ 0 →
    {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
      p.1 + p.2 = t ∧ binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

/--
Resolved true: Resolved true (Cusick 2026): complete proof of the exact modular pair-count
inequality (k>=2, 1<=t<M, weight bound, 2^(k-1) cap). Source: T. W. Cusick, Proof of the Tu-Deng
Conjecture, arXiv:2608.14821 (2026), https://arxiv.org/abs/2608.14821. Moved from
`OpenConjectures/NumberTheory/TuDengConjecture`.
-/
public theorem_wanted tuDengConjecture_holds : tuDengConjecture

end MathlibExt.NumberTheory.TuDengConjectureWanted
