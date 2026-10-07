/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.CycleContinuousAntichainWanted

/-! UnsolvedMath record `OPG-323__3223`. -/


/-- Multigraph with vertices `V`, edges `E`, and endpoint incidence `ends`,
allowing parallel edges and loops. Source: [OPG-323] Antichains in the cycle
continuous order (URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
structure FGraph where
  V : Type
  E : Type
  ends : E → V × V

/-- Finite graphs with at least one edge, the domain of the cycle-continuous
order. Source: [OPG-323] (URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
def IsFiniteNontrivial (G : FGraph) : Prop :=
  Finite G.V ∧ Finite G.E ∧ Nonempty G.E

/-- Binary cycle space: finite edge-sets with even degree at every vertex;
loops contribute two and hence are even. Source: [OPG-323] (URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def cycleSpace (G : FGraph) : Set (Set G.E) :=
  {S | Set.Finite S ∧ ∀ v : G.V, Even (Set.ncard {e ∈ S | ((G.ends e).1 = v ∧ (G.ends e).2 ≠ v) ∨ ((G.ends e).1 ≠ v ∧ (G.ends e).2 = v)})}

/-- Cycle-continuous map: preimage of every binary cycle in `H` is a binary
cycle in `G`. Source: [OPG-323] (URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def IsCycleContinuous (G H : FGraph) (f : G.E → H.E) : Prop :=
  ∀ C ∈ cycleSpace H, f ⁻¹' C ∈ cycleSpace G

/-- Existence of an infinite pairwise cycle-incomparable family of finite
graphs with at least one edge. Source: [OPG-323] (URL: http://www.openproblemgarden.org/op/antichains_in_the_cycle_continuous_order). -/
noncomputable def conjecture : Prop :=
  ∃ G : ℕ → FGraph, (∀ n, IsFiniteNontrivial (G n)) ∧ Function.Injective G ∧ ∀ i j, i ≠ j → ¬∃ f : (G i).E → (G j).E, IsCycleContinuous (G i) (G j) f
/--
Resolved true: Robert Samal (arXiv:1212.6909, 2012; J. Graph Theory 2017), Theorem 1.3,
constructs an infinite set of cubic bridgeless graphs that are pairwise incomparable under
cycle-continuous maps (preimage of every even-degree edge set is even), answering the
DeVos-Nesetril-Raspaud antichain question positively. Source: Robert Samal, Cycle-continuous
mappings - order structure, Journal of Graph Theory 85 (2017) 56-73, arXiv:1212.6909,
https://arxiv.org/abs/1212.6909. Moved from
`OpenConjectures/GraphTheory/CycleContinuousAntichain`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.CycleContinuousAntichainWanted
