/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.Bridgeless

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An edgeless graph is bridgeless. -/
example (h : G.edgeSet = ∅) : G.IsBridgeless := by
  intro e he
  rw [h, Set.mem_empty_iff_false] at he
  exact he.elim

example (V : Type*) : (⊥ : SimpleGraph V).IsBridgeless :=
  isBridgeless_bot V

example {V : Type*} {G : SimpleGraph V} (h : G.IsBridgeless) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : ¬ G.IsBridge e :=
  h.not_isBridge he

example {V : Type*} {G : SimpleGraph V} (h : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    G.IsBridgeless :=
  IsBridgeless.mk h

example {V : Type*} {G : SimpleGraph V} :
    G.IsBridgeless ↔ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  isBridgeless_iff

end SimpleGraph
