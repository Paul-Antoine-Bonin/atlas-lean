/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Forcing a 2-regular minor by average degree (OPG-59911)

Every graph of average degree at least `4t/3 - 2` contains every 2-regular
graph on `t` vertices as a minor.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.TwoRegularMinorForcingWanted

/-! Source record `OPG-59911`. -/

/-- Branch-set model of a general minor: nonempty, connected, pairwise disjoint
vertex sets indexed by `H`'s vertices, with an edge across each edge of `H`. -/
def HasMinor {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  ∃ branch : W → Finset V,
    (∀ w, (branch w).Nonempty) ∧
      (∀ w, (G.induce (branch w : Set V)).Connected) ∧
      (∀ u v, u ≠ v → Disjoint (branch u) (branch v)) ∧
      ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- [OPG-59911] Every finite graph of average degree at least `4t/3 - 2`
contains every 2-regular graph on `t` vertices as a minor. -/
def conjecture : Prop :=
  ∀ (t : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ((∑ v : V, (G.degree v : ℚ)) / (Fintype.card V : ℚ) ≥ 4 * (t : ℚ) / 3 - 2) →
    ∀ (H : SimpleGraph (Fin t)) [DecidableRel H.Adj], (∀ v, H.degree v = 2) → HasMinor G H

/--
Resolved true: Csoka, Lo, Norin, Wu and Yepremyan (J. Combin. Theory Ser. B 2017,
arXiv:1509.01185) prove c(H) <= (v(H)+comp(H))/2 - 1 for unions of cycles, verifying the
Reed-Wood conjecture; their e/(v-1) form (Corollary 8, Lemma 9) also covers the non-strict
4t/3-2 average-degree threshold. Source: Endre Csoka, Irene Lo, Sergey Norin, Hehui Wu and Liana
Yepremyan, The extremal function for disconnected minors, Journal of Combinatorial Theory Series
B (2017), arXiv:1509.01185, https://arxiv.org/abs/1509.01185. Moved from
`OpenConjectures/GraphTheory/TwoRegularMinorForcing`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.TwoRegularMinorForcingWanted
