/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import MathlibExt.NumberTheory.CountingOppermannPrimes

namespace MetaMathlibExt

@[expose] public section

/-- The two prime counts in the closed intervals adjacent to `n²` are each
asymptotic to `n / (2 log n)`.

Source: Joel E. Cohen, *Conjectures about Primes and Cyclic Numbers*,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.tex>.
Concept `jis_sem_b1c5531b893b694777f2c1c5`; statement
`jis_6984ebbf83b6eb73fb1b156d`. -/
theorem_wanted oppermannPrimeCountConjecture :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (oppermannLowerPrimeCount n : ℝ))
      (fun n : ℕ => oppermannAsymptotic n) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (oppermannUpperPrimeCount n : ℝ))
      (fun n : ℕ => oppermannAsymptotic n)

end

end MetaMathlibExt
