/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

namespace MetaMathlibExt

@[expose]
public section

/-- Cohen's Oppermann analog for cyclic numbers: both open intervals around
`n²` contain a cyclic number, while the counts in the corresponding closed
intervals have the two stated asymptotic descriptions.

Stable source identifiers: concept `jis_sem_804f8a678da69b6636b615f6`;
statement `jis_b6b3211114727e0910c9b5bb`, conjecture `conj:Oppermann` and
equations `eq:CyclicsInSquaresUsingPollackLeft` and
`eq:CyclicsInSquaresUsingPollackRight`.
-/
theorem_wanted oppermannAnalogForCyclicNumbers :
    (∀ n : ℕ, 1 < n →
      ∃ c c' : ℕ, IsCyclicNumber c ∧ n ^ 2 - n < c ∧ c < n ^ 2 ∧
        IsCyclicNumber c' ∧ n ^ 2 < c' ∧ c' < n ^ 2 + n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => (oppermannCyclicCountLeft n : ℝ))
      (fun n => oppermannCyclicLeftApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => oppermannCyclicLeftApproximation n)
      (fun n => oppermannCyclicApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => (oppermannCyclicCountRight n : ℝ))
      (fun n => oppermannCyclicRightApproximation n) ∧
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n => oppermannCyclicRightApproximation n)
      (fun n => oppermannCyclicApproximation n)

end

end MetaMathlibExt
