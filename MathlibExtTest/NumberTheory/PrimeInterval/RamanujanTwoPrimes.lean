/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeInterval.RamanujanTwoPrimes

@[expose] public section

namespace MathlibExtTest.NumberTheory.PrimeInterval.RamanujanTwoPrimes

#check MathlibExt.NumberTheory.BreuschWanted.ramanujan_two_primes_between

example : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 6 < p ∧ p < q ∧ q < 2 * 6 :=
  MathlibExt.NumberTheory.BreuschWanted.ramanujan_two_primes_between 6 (by decide)

end MathlibExtTest.NumberTheory.PrimeInterval.RamanujanTwoPrimes
