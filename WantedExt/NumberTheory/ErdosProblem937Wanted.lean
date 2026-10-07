/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 937
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.KFull

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem937Wanted

/-! Source record `FC-ErdosProblem937`, ported from FormalConjectures
`ErdosProblems/937.lean` (`def IsCoprimePowerfulAP4`,
`theorem erdos_937`) and checked against erdosproblems.com/937. The
upstream `answer(True)` is dropped; the right-hand side is stated
directly. The canonical `Nat.IsKFull 2` predicate is reused. Status:
resolved true (Bajpai–Bennett–Chan [BBC24]); the registry links a
proof-bearing external Lean development. -/

/-- The four numbers `a, a+d, a+2d, a+3d` form a four-term arithmetic
progression (`d > 0`) of pairwise coprime powerful numbers. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  Nat.IsKFull 2 a ∧ Nat.IsKFull 2 (a + d) ∧ Nat.IsKFull 2 (a + 2 * d) ∧
  Nat.IsKFull 2 (a + 3 * d) ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

/-- There are infinitely many four-term arithmetic progressions of pairwise
coprime powerful numbers. -/
def conjecture : Prop :=
  {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite

/--
Resolved true: Resolved true by Bajpai–Bennett–Chan; a proof is available in an external Lean
development. Source: Prajeet Bajpai, Michael A. Bennett, and Tsz Ho Chan, Arithmetic
progressions in squarefull numbers, International Journal of Number Theory 20 (2024), 19–45,
https://mathscinet.ams.org/mathscinet-getitem?mr=4688726. Moved from
`OpenConjectures/NumberTheory/ErdosProblem937`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem937Wanted
