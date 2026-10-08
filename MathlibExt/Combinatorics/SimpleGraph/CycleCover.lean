/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Multiset.Basic

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A cycle in a graph, presented as a closed walk with a cycle proof. -/
structure Cycle (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

/-- The edges traversed by a cycle. -/
def Cycle.edges {G : SimpleGraph V} (c : Cycle G) : List (Sym2 V) :=
  c.walk.edges

/-- The length of a cycle. -/
def Cycle.length {G : SimpleGraph V} (c : Cycle G) : ℕ :=
  c.walk.length

/-- `C` covers `G`: every edge of `G` lies on at least one cycle of `C`. -/
def IsCycleCover (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeFinset, ∃ c ∈ C, e ∈ c.edges

/-- The total length of a multiset of cycles. -/
def totalLength {G : SimpleGraph V} (C : Multiset (Cycle G)) : ℕ :=
  (C.map Cycle.length).sum

end SimpleGraph
