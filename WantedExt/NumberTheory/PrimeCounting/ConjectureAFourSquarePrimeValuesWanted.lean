/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Infinitely many `k : ℕ` make `4 * k ^ 2 + 2 * k + 1` prime. The source
derives this from its Conjecture A (Bunyakovsky); formalized here as the
infinitude statement alone (a conjecture, not proved here). Scope is only the
`4 * k ^ 2 + 2 * k + 1` polynomial (source equation `eq:p`), not the full
Bunyakovsky conjecture nor the `9 * k ^ 2 + 6 * k + 2` sibling.

Source: Jean-Marie De Koninck and Matthieu Moineau, "Consecutive Integers
Divisible by a Power of their Largest Prime Factor", Journal of Integer
Sequences 21 (2018), Article 18.9.3, lines 239–242,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/DeKoninck/dek22.tex>.
-/
theorem_wanted conjectureA_prime_values_four_square :
    Set.Infinite {k : ℕ | Nat.Prime (4 * k ^ 2 + 2 * k + 1)}

end

end MetaMathlibExt
