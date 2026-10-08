/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.GraphMinor
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- Robertson–Seymour graph minors theorem (statement `robertson-seymour-s1` in the
supplied source): the minor relation (`MetaMathlibExt.IsMinor` on bundled finite
simple graphs) is a partial order on finite graphs up to graph isomorphism
(mutual minors are isomorphic), and every minor-closed family `F` of finite graphs
is characterized by a finite set of forbidden minors: `G` is in `F` iff no
forbidden minor is a minor of `G`.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
theorem_wanted robertson_seymour
    (F : Set FinGraph)
    (h_closed : ∀ G H, IsMinor H G → G ∈ F → H ∈ F) :
    (∀ G H : FinGraph, IsMinor G H → IsMinor H G →
      Nonempty (G.G ≃g H.G)) ∧
    ∃ (Obstructions : Set FinGraph) (_ : Obstructions.Finite),
      ∀ G, G ∈ F ↔ ∀ H ∈ Obstructions, ¬IsMinor H G

end MetaMathlibExt
