/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jaeger's modular orientation conjecture
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.JaegerModularOrientationWanted

/-! Source record `OPG-130`.

We represent a finite undirected multigraph by finite types of vertices and edges together with
two endpoint maps. The endpoint order is only a reference orientation: `isReversed` below chooses
an orientation independently for each edge. This representation allows parallel edges and loops.
-/

/-- An edge crosses a vertex cut when exactly one of its endpoints lies on the chosen side. -/
def CrossesCut {V E : Type} (end₁ end₂ : E → V) (S : Set V) (e : E) : Prop :=
  (end₁ e ∈ S ∧ end₂ e ∉ S) ∨ (end₁ e ∉ S ∧ end₂ e ∈ S)

/-- The number of edges crossing a cut. Distinct parallel edges are counted separately. -/
noncomputable def cutSize {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (S : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (CrossesCut end₁ end₂ S)).card

/-- Edge-connectivity at least `4 * k`, expressed through nontrivial cuts.

The multigraph has at least two vertices, and every cut whose two sides are nonempty has at least
`4 * k` crossing edges. Thus connectedness is included in the cut condition.
-/
noncomputable def IsFourKEdgeConnected {V E : Type} [Fintype V] [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) : Prop :=
  2 ≤ Fintype.card V ∧
    ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 4 * k ≤ cutSize end₁ end₂ S

/-- The tail of an edge after applying the chosen reorientation. -/
def orientedTail {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₂ e else end₁ e

/-- The head of an edge after applying the chosen reorientation. -/
def orientedHead {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₁ e else end₂ e

/-- The indegree of a vertex in the chosen orientation. -/
noncomputable def indegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedHead end₁ end₂ isReversed e = v)).card

/-- The outdegree of a vertex in the chosen orientation. -/
noncomputable def outdegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedTail end₁ end₂ isReversed e = v)).card

/-- Every vertex has indegree minus outdegree equal to zero modulo `2 * k + 1`. -/
noncomputable def IsModularOrientation {V E : Type} [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) (isReversed : E → Bool) : Prop :=
  ∀ v : V,
    (indegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) -
        (outdegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) = 0

/-- Jaeger's modular orientation conjecture.

The parameter `k` is positive, as in the source discussion of `(2 + 1 / k)`-flows and its
specializations at `k = 1` and `k = 2`.
-/
def conjecture : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ (V E : Type) [Fintype V] [Fintype E] (end₁ end₂ : E → V),
      IsFourKEdgeConnected k end₁ end₂ →
        ∃ isReversed : E → Bool, IsModularOrientation k end₁ end₂ isReversed

/--
Resolved false: Han, Li, Wu and Zhang (J. Combin. Theory Ser. B 131 (2018) 1-11) construct, for
every k >= 3, a 4k-edge-connected graph with no circular (2+1/k)-flow, equivalently no modulo
(2k+1) orientation, refuting the all-k statement; k=1 (Tutte's 3-flow conjecture) and k=2 remain
open. Source: Daniel W. Cranston and Jiaao Li, Circular flows in planar graphs, SIAM J. Discrete
Math. (2020), arXiv:1812.09833, https://arxiv.org/abs/1812.09833. Moved from
`OpenConjectures/Combinatorics/JaegerModularOrientation`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.JaegerModularOrientationWanted
