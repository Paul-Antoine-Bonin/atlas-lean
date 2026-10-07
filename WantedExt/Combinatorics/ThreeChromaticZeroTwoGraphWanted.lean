/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three-chromatic (0,2)-graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted

/-! UnsolvedMath record `OPG-562`.

The problem-page discussion notes that infinite three-chromatic `(0,2)`-graphs
are easy to construct; the open question concerns finite graphs, represented
here by the vertex type `Fin n`.
-/

/-- Every pair of distinct vertices has either zero or two common neighbors. -/
def IsZeroTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    (G.commonNeighbors u v).ncard = 0 ∨
      (G.commonNeighbors u v).ncard = 2

/-- There exists a finite `(0,2)`-graph with chromatic number exactly three. -/
noncomputable def conjecture : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsZeroTwo G ∧ G.chromaticNumber = 3

/--
Resolved false: Williamson (arXiv:2607.10125, July 2026, Theorem 2) proves every finite
three-colourable (0,2)-graph is bipartite, so no finite (0,2)-graph has chromatic number exactly
three; the target's existence claim is false. Source: Christopher Williamson, Finite
Three-Colourable (0,2)-Graphs Are Bipartite, arXiv preprint (2026), arXiv:2607.10125,
https://arxiv.org/abs/2607.10125. Moved from
`OpenConjectures/Combinatorics/ThreeChromaticZeroTwoGraph`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted
