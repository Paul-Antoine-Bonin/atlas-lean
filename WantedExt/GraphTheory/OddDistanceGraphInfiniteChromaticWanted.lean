/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd distance graph has infinite chromatic number
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted

/-! Source record `OPG-616`. Validated from hill-photon submission. -/

namespace ODGIC

/-!
# Clause inventory for [OPG-616]

- Object: `O`, graph on `ℝ²` (as `EuclideanSpace ℝ (Fin 2)`).
- Hypothesis: adjacency iff distance is an odd integer (odd `ℕ`
  suffices since distances are nonnegative).
- Question: `χ(O) = ∞` as `chromaticNumber = ⊤`.
-/

/-- The odd distance graph on `ℝ²` (record OPG-616). -/
noncomputable def OddDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := ∃ k : ℕ, Odd k ∧ dist x y = (k : ℝ)
  symm := ⟨by
    intro x y h
    obtain ⟨k, hk, hkk⟩ := h
    exact ⟨k, hk, by rw [dist_comm]; exact hkk⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨k, hk, hkk⟩ := h
    rw [dist_self] at hkk
    have hk0 : k = 0 := by exact_mod_cast hkk.symm
    rw [hk0] at hk
    exact Nat.not_odd_zero hk⟩

/-- Question: is `χ(O) = ∞`? (record OPG-616) -/
def OddDistanceChromaticInfinite : Prop := OddDistanceGraph.chromaticNumber = ⊤

end ODGIC

/--
Resolved true: James Davies (Odd distances in colourings of the plane, GAFA 34 (2024);
arXiv:2209.15598), Theorem 1, proves every finite colouring of the plane has a monochromatic
pair at odd integer distance, so the odd distance graph has no finite colouring and its
chromatic number is infinite (countable). Source: James Davies, Odd distances in colourings of
the plane, Geometric and Functional Analysis 34 (2024) 19-31, arXiv:2209.15598,
https://arxiv.org/abs/2209.15598. Moved from
`OpenConjectures/GraphTheory/OddDistanceGraphInfiniteChromatic`.
-/
public theorem_wanted OddDistanceChromaticInfinite_holds : ODGIC.OddDistanceChromaticInfinite

end MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted
