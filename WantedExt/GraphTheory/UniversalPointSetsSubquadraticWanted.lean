/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Universal point sets of subquadratic size for planar graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.UniversalPointSetsSubquadraticWanted

/-! Source record `GRAPH-022`. -/

namespace UPSS

/-!
# Clause inventory for [GRAPH-022]

- Quantifier domain: planar graphs (straight-line crossing-free
  embeddable) on `Fin n` vertices.
- Object: plane point sets (`Finset (ℝ × ℝ)`).
- Object: straight-line embeddings (injective, crossing-free, no
  vertex on a non-incident edge).
- Question: subquadratic-size universal point sets exist
  (`f n / n^2 → 0` with `P.card ≤ f n`).
-/

/-- Crossing-free straight-line embedding of a graph, with edge segments
given by the canonical `SimpleGraph.Segment` [GRAPH-022]. -/
def IsStraightLinePlanarEmbedding {V : Type} (G : SimpleGraph V)
    (pos : V → ℝ × ℝ) : Prop :=
  Function.Injective pos ∧
  (∀ u v x y : V, G.Adj u v → G.Adj x y →
    (u ≠ x ∨ v ≠ y) → (u ≠ y ∨ v ≠ x) →
    ∀ p : ℝ × ℝ, p ∈ SimpleGraph.Segment (pos u) (pos v) →
      p ∈ SimpleGraph.Segment (pos x) (pos y) →
      ∃ z : V, (z = u ∨ z = v) ∧ (z = x ∨ z = y) ∧ p = pos z) ∧
  (∀ u v w : V, G.Adj u v → w ≠ u → w ≠ v →
    pos w ∉ SimpleGraph.Segment (pos u) (pos v))

/-- Universality of a point set for `n`-vertex planar graphs [GRAPH-022]. -/
def IsUniversalPointSet (P : Finset (ℝ × ℝ)) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), SimpleGraph.IsPlanar G →
    ∃ pos : Fin n → ℝ × ℝ,
      IsStraightLinePlanarEmbedding G pos ∧ ∀ v, pos v ∈ P

/-- Existence of subquadratic-size universal point sets for planar graphs
[GRAPH-022]. -/
def ExistsSubquadraticUniversalPointSet : Prop :=
  ∃ f : ℕ → ℕ,
    Filter.Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 0) ∧
    ∀ n, ∃ P : Finset (ℝ × ℝ), P.card ≤ f n ∧ IsUniversalPointSet P n

end UPSS

/--
Resolved true: Taylor Gordon (arXiv:2609.10916, Sept 2026), Theorem 1, constructs universal
point sets of size n exp(O(sqrt(log n))) = n^{1+o(1)} for n-vertex planar graphs via a layered
interval family giving small S_n(213)-superpatterns and the Bannister-Cheng-Devanny-Eppstein
reduction; this is o(n^2). Source: Taylor Gordon, Almost Linear Universal Point Sets for Planar
Graphs, arXiv preprint (2026), arXiv:2609.10916, https://arxiv.org/abs/2609.10916; Michael J.
Bannister, Zhanpeng Cheng, William E. Devanny and David Eppstein, Superpatterns and Universal
Point Sets, arXiv:1308.0403, https://arxiv.org/abs/1308.0403. Moved from
`OpenConjectures/GraphTheory/UniversalPointSetsSubquadratic`.
-/
public theorem_wanted ExistsSubquadraticUniversalPointSet_holds : UPSS.ExistsSubquadraticUniversalPointSet

end MathlibExt.GraphTheory.UniversalPointSetsSubquadraticWanted
