/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.Balanced

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (h : (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ)) :
    SimpleGraph.IsBalanced G 1 := h

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    SimpleGraph.IsBalanced G 1 ↔
      (G.maxDegree : ℝ) ≤ 1 * (G.minDegree : ℝ) :=
  Iff.rfl
