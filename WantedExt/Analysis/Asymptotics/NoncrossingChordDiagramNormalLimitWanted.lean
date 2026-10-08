/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open scoped BigOperators
open Filter Topology

namespace MetaMathlibExt

/--
The short-chord count in a uniformly chosen non-crossing linear `k`-chord diagram is
asymptotically normal with the stated mean and variance.

Source: Donovan Young, "Linear k-Chord Diagrams", Journal of Integer Sequences 23 (2020), Article 20.9.1, Theorem lines 1014-1024 (§6.1), <https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex>.
-/
public theorem_wanted
    noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal
    (k : ℕ) (hk : 2 ≤ k) (T : ℕ → ℕ → ℕ)
    (hT : T 0 0 = 1 ∧
      (∀ ℓ, 0 < ℓ → T 0 ℓ = 0) ∧
      ∀ n ℓ,
        T (n + 1) ℓ =
          (∑ m : Fin k → Fin (n + 1),
            ∑ s : Fin k → Fin (ℓ + 1),
              if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (s i : ℕ)) = ℓ then
                ∏ i, T (m i) (s i)
              else 0) - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1)) :
    let mean : ℕ → ℝ := fun n =>
      (((((k - 1 : ℕ) : ℝ) / (k : ℝ)) ^ (k - 1)) * n)
    let variance : ℕ → ℝ := fun n =>
      (((((k - 1 : ℕ) : ℝ) / (k : ℝ)) ^ (2 * k)) *
        (k : ℝ) / (((k - 1 : ℕ) : ℝ) ^ 2) *
        (1 - 2 * (k : ℝ) +
          ((k - 1 : ℕ) : ℝ) *
            (((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ^ k)) * n)
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ =>
          (∑ ℓ ∈ Finset.range (n + 1),
              (T n ℓ : ℝ) *
                Real.exp
                  (t * (((ℓ : ℝ) - mean n) / Real.sqrt (variance n)))) /
            ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ))
        atTop
        (nhds (Real.exp (t ^ 2 / 2)))

end MetaMathlibExt
