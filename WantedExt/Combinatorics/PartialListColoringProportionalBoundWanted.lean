/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partial list coloring proportional bound
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

namespace MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted

/-- A vertex subset `S` is partially list-colorable from `lists` when the induced
subgraph on `S` admits a proper coloring choosing each vertex color from its list.
The coloring is defined only on the subtype `S`, so no colors are required
outside `S`. -/
def IsPartialListColoring {V C : Type*} [DecidableEq C]
    (G : SimpleGraph V) (lists : V → Finset C) (S : Finset V) : Prop :=
  ∃ color : S → C, (∀ v : S, color v ∈ lists (v : V)) ∧
    (∀ v w : S, G.Adj (v : V) (w : V) → color v ≠ color w)

/-- Albertson–Grossman–Haas partial list coloring conjecture: for a finite simple
graph with list chromatic number `q`, every exact `t`-list assignment with
`t ≤ q` permits a proper coloring of a vertex subset `S` with
`t * n ≤ q * S.card`, i.e. `S.card ≥ t * n / q` over the rationals. The
positivity hypothesis records the denominator convention and, together with
`IsChoiceNumber`, excludes the empty-graph degeneracy. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ),
    0 < q → G.IsChoiceNumber q →
    ∀ (t : ℕ), t ≤ q →
    ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, (lists v).card = t) →
    ∃ S : Finset V, IsPartialListColoring G lists S ∧ t * Fintype.card V ≤ q * S.card

/--
Resolved false: Noel (arXiv:2609.23291, Sep 2026) gives a 14-vertex graph with list chromatic
number 3 and an exact 2-list assignment from which at most 9 < 28/3 vertices can be properly
coloured, falsifying the target at q = 3, t = 2. Source: Jonathan A. Noel, The Partial List
Colouring Conjecture is False, arXiv preprint (2026), arXiv:2609.23291,
https://arxiv.org/abs/2609.23291. Moved from
`OpenConjectures/Combinatorics/PartialListColoringProportionalBound`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted
