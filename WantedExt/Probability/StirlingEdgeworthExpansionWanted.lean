/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling

@[expose] public section

open Filter Finset Set
open scoped BigOperators Topology

namespace MetaMathlibExt

/-! # Stirling–Edgeworth expansion for Ewens sampling occupancy
-/

/--
The local Edgeworth expansion of the Ewens sampling occupancy probability mass
function `P(K_n(θ) = k) = θ^k [n,k] / θ^{(n)}`, uniformly over the parameter
on compact subsets of the positive reals and over all values in its support:
`(log n)^{(r+1)/2} sup_k |PMF − Gaussian × ∑_{j≤r} H_j/(θ log n)^{j/2}| → 0`,
stated in ε–N form with the coefficient functions `H` existentially bound.

Source: Zakhar Kabluchko, Alexander Marynych, and Henning Sulzbach, "Mode and
Edgeworth Expansion for the Ewens Distribution and the Stirling Numbers,"
Journal of Integer Sequences 19 (2016), Article 16.8.8, Theorem (label
`theo:stirling_edgeworth`), lines 207–226 (Ewens probability mass function at
lines 143–146),
https://cs.uwaterloo.ca/journals/JIS/VOL19/Kabluchko/kabl2.tex
-/
public theorem_wanted stirling_edgeworth_expansion
    (r : ℕ)
    (L : Set ℝ)
    (hL_compact : IsCompact L)
    (hL_positive : L ⊆ Set.Ioi 0) :
    ∃ H : ℕ → ℝ → ℝ → ℝ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ θ ∈ L, ∀ k ∈ Finset.Icc 1 n,
        Real.rpow (Real.log n) (((r : ℝ) + 1) / 2) *
            |θ ^ k * (Nat.stirlingFirst n k : ℝ) /
                (∏ i ∈ Finset.range n, (θ + (i : ℝ))) -
              Real.exp (-(((((k : ℝ) - θ * Real.log n) /
                  Real.sqrt (θ * Real.log n)) ^ 2) / 2)) /
                Real.sqrt (2 * Real.pi * θ * Real.log n) *
                ∑ j ∈ Finset.range (r + 1),
                  H j (((k : ℝ) - θ * Real.log n) /
                    Real.sqrt (θ * Real.log n)) θ /
                    Real.rpow (θ * Real.log n) ((j : ℝ) / 2)| < ε

end MetaMathlibExt
