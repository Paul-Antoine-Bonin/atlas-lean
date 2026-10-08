/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs

namespace MetaMathlibExt

@[expose] public section

/-- Product of the nonzero base-`b` digits of `n`. -/
public def nonzeroDigitProd (b n : ℕ) : ℕ :=
  ((Nat.digits b n).filter (· != 0)).prod

/-- A positive integer `n` is `b`-prodigious iff `2 ≤ b`, `0 < n`,
and `n` is divisible by the product of its nonzero base-`b` digits. -/
public def IsProdigious (b n : ℕ) : Prop :=
  2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n

public instance instDecidableIsProdigious (b n : ℕ) :
    Decidable (IsProdigious b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n))

end

end MetaMathlibExt
