/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexTransitive

@[expose] public section

open SimpleGraph

example (G : SimpleGraph (Fin 1)) : G.IsVertexTransitive := by simp
