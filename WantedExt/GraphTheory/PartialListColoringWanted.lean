/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partial List Coloring
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Rat.Cast.Order
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

namespace MathlibExt.GraphTheory.PartialListColoringWanted

/-! Source record `OPG-788`. Iradmusa's partial list coloring monotonicity conjecture
from the Open Problem Garden (posted May 12th, 2008): the ratio `λ_t / t` is
nonincreasing in `t` up to the list chromatic number. -/

/-- A proper coloring of the vertex subset `S` respecting the list assignment `L`:
every vertex of `S` gets a color from its own list, and adjacent vertices get distinct colors. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- `lambdaMax G L` is `λ_L`: the maximum number of vertices of `G` colorable
with respect to the list assignment `L` (the largest `k` for which some
`k`-element subset admits a proper list coloring). -/
noncomputable def lambdaMax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, ∃ f : V → ℕ, S.card = k ∧ IsListColoring G L f S}

/-- `lambdaMin G t` is `λ_t`: the minimum of `λ_L` over all list assignments
`L` with every list of size `t`. -/
noncomputable def lambdaMin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : V → Finset ℕ, (∀ v, (L v).card = t) ∧ lambdaMax G L = k}

/-- Iradmusa's conjecture: for a graph with choice number `χ_ℓ` (via the
shared `SimpleGraph.IsChoiceNumber` predicate) and `1 ≤ r ≤ s ≤ χ_ℓ`, one
has `λ_r / r ≥ λ_s / s`. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ_ℓ r s : ℕ),
    G.IsChoiceNumber χ_ℓ →
    1 ≤ r → r ≤ s → s ≤ χ_ℓ →
    (lambdaMin G r : ℚ) / (r : ℚ) ≥ (lambdaMin G s : ℚ) / (s : ℚ)

/--
Resolved false: Noel (arXiv:2609.23291, Sept 2026), Theorem 1.1, gives a 14-vertex graph (four
triangles plus two terminals) with list chromatic number 3 and a 2-list assignment colouring at
most 9 vertices, so lambda_2/2 <= 9/2 < 14/3 = lambda_3/3, refuting the ratio conjecture at r=2,
s=3. Source: Jonathan A. Noel, The Partial List Colouring Conjecture is False, arXiv preprint
(2026), arXiv:2609.23291, https://arxiv.org/abs/2609.23291. Moved from
`OpenConjectures/GraphTheory/PartialListColoring`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.PartialListColoringWanted
