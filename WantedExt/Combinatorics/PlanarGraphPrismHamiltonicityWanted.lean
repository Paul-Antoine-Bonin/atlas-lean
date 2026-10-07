/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hamiltonicity of prisms over 3-connected planar graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

@[expose] public section

namespace MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicityWanted

/-! Source record `OPG-47285`. -/

/-- The prism over every finite 3-connected planar graph has a Hamilton cycle. -/
def conjecture : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    SimpleGraph.IsVertexConnected 3 G → SimpleGraph.IsPlanar G →
      (G □ SimpleGraph.completeGraph (Fin 2)).IsHamiltonian

/--
Resolved false: Spacapan constructed a 3-connected planar graph whose prism is not Hamiltonian,
refuting the universal statement. Source: S. Špacapan, A counterexample to prism-hamiltonicity
of 3-connected planar graphs, Journal of Combinatorial Theory, Series B 148 (2021), 46–52,
https://arxiv.org/abs/1906.06683. Moved from
`OpenConjectures/Combinatorics/PlanarGraphPrismHamiltonicity`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.PlanarGraphPrismHamiltonicityWanted
