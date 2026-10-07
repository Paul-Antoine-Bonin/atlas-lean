/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.Degeneracy

@[expose] public section

namespace SimpleGraph

example {V : Type*} [Finite V] (U : Set V) : (⊥ : SimpleGraph V).IsDegenerateOn U 0 := by
  intro W hWne _
  obtain ⟨v, hvW⟩ := hWne
  refine ⟨v, hvW, ?_⟩
  simp

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k l : ℕ}
    (h : G.IsDegenerateOn U k) (hkl : k ≤ l) : G.IsDegenerateOn U l :=
  h.mono hkl

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k : ℕ}
    (h : G.IsDegenerate k) : G.IsDegenerateOn U k :=
  h.isDegenerateOn U

end SimpleGraph

end
