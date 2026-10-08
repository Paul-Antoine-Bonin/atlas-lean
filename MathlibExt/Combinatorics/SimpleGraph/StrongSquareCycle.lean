/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Square

/-!
# Rooted Hamiltonian cycles in graph squares
-/

@[expose] public section

namespace SimpleGraph

/-- A Hamiltonian cycle in the square whose two edges at `x` come from the original graph. -/
public def HasStrongSquareCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : Prop :=
  ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x

/-- A strong square cycle consists of a Hamiltonian cycle with original edges at the root. -/
public theorem hasStrongSquareCycle_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) :
    G.HasStrongSquareCycle x ↔
      ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
        G.Adj x p.snd ∧ G.Adj p.penultimate x :=
  Iff.rfl

end SimpleGraph
