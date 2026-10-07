/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OEIS A022030
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA022030Wanted

/-! Source record `FC-OeisA022030`, ported from FormalConjectures
`OEIS/22030.lean` and checked against oeis.org/A022030. A nonlinear
recurrence sequence (core Lean only). Test evaluations omitted (proofs
live upstream). Status: resolved true (Barker's linear recurrence holds;
formal proof upstream). -/

/-- A nonlinear recurrence sequence. -/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

/-- The sequence satisfies a linear recurrence from `n ≥ 4`. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (_hn : 4 ≤ n),
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

/--
Resolved true: Barker's (2012) linear recurrence holds (formal proof upstream). Source: Kenta
Kitamura, Lean formal proof of Barker's linear recurrence,
https://github.com/KitaKen1/oeis-a022030-lean/blob/f74afc2/lean/OeisA022030FC.lean#L270-L275.
Moved from `OpenConjectures/NumberTheory/OeisA022030`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.OeisA022030Wanted
