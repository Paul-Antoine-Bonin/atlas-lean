/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple

namespace MetaMathlibExt

@[expose] public section

/-- The Hardy–Littlewood prime-tuple conjecture for a nonempty tuple of
distinct integers: the singular series is nonzero and the prime-tuple count
has the predicted asymptotic.

Source: Hùng Việt Chu, Nathan McNew, Steven J. Miller, Victor Xu, and Sean Zhang,
*When Sets Can and Cannot Have Sum-Dominant Subsets*,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Miller/miller8.tex>.
Concept `jis_sem_c814202d5e6a0edd6fed8bb5`; statement
`jis_43e1aedfa0e84467b1f1765e`. -/
theorem_wanted hardyLittlewoodPrimeTupleConjecture
    (m : ℕ) (hm : 0 < m) (b : Fin m → ℤ) (hb : Function.Injective b)
    (hadmissible : IsHardyLittlewoodAdmissible m b) :
    hardyLittlewoodSingularSeries m b ≠ 0 ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun x : ℕ => (hardyLittlewoodPrimeTupleCount m b x : ℝ))
        (fun x : ℕ => hardyLittlewoodSingularSeries m b *
          ∫ u in (2 : ℝ)..(x : ℝ), 1 / (Real.log u) ^ m)

end

end MetaMathlibExt
