/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nonseparating planar continuum [OPG-37295]

Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

namespace MathlibExt.Topology.NonseparatingPlanarContinuumWanted

/-!
[OPG-37295] Nonseparating planar continuum.
Source: Open Problem Garden, node ID 37295,
http://www.openproblemgarden.org/op/nonseparating_planar_continuum.

Clause list (every item appears in the formal text below):
- (C1) Domain: `K` is a set in the plane
  (`EuclideanSpace ℝ (Fin 2)`).
- (C2) `K` is compact (`IsCompact`).
- (C3) `K` is path-connected (`IsPathConnected`). Mathlib's
  `IsPathConnected K` asserts a point of `K`, so `K` is nonempty and
  the empty set (which lacks the fixed point property) is excluded.
- (C4) `K` does not separate the plane: its complement is connected
  (`IsConnected Kᶜ`).
- (C5) Claim: every such `K` has the fixed point property, i.e. every
  continuous self-map of `K` has a fixed point.
- Status: posed as a question-Prop; the file asserts no answer.
-/

/-- Has the fixed point property (OPG-37295, node ID 37295): every
continuous map from `K` into itself has a fixed point. -/
def HasFixedPointProperty (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ f : (↥K → ↥K), Continuous f → ∃ x : ↥K, f x = x

/-- Nonseparating planar continuum conjecture (OPG-37295, node ID
37295): any path-connected, compact set in the plane which does not
separate the plane has the fixed point property. Stated as a
proposition. -/
def conjecture : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 2)),
    IsCompact K → IsPathConnected K → IsConnected Kᶜ → HasFixedPointProperty K

/--
Resolved true: Hagopian (A fixed-point theorem for plane continua, Bull. AMS 77 (1971), 351-354;
addendum 1972) proved that every arcwise connected nonseparating plane continuum has the fixed
point property; path-connected compact plane sets are arcwise connected, so the Lean statement
holds. Source: A. M. Blokh, R. J. Fokkink, J. C. Mayer, L. G. Oversteegen, E. D. Tymchatyn,
Fixed point theorems for plane continua with applications, Mem. Amer. Math. Soc. 224 (2013), no.
1053, arXiv:1004.0214 (citing C. L. Hagopian, Bull. Amer. Math. Soc. 77 (1971), 351-354),
https://arxiv.org/abs/1004.0214. Moved from
`OpenConjectures/Topology/NonseparatingPlanarContinuum`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Topology.NonseparatingPlanarContinuumWanted
