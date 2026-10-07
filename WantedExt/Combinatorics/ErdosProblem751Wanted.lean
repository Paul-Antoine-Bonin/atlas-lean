/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 751
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Circumference

@[expose] public section

open Filter

namespace MathlibExt.Combinatorics.ErdosProblem751Wanted

/-! Source record `FC-ErdosProblem751`, ported from FormalConjectures
`ErdosProblems/751.lean` and checked against erdosproblems.com/751.
`SimpleGraph.cycleLengths` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`).
The two original arbitrarily-large-gap propositions are preserved without
their `answer(False)` wrappers. Status: resolved false by Bondy--Vince. -/

/-- Chromatic-number-four graphs with arbitrarily large cycle-length gaps,
with and without a prescribed girth lower bound. -/
def conjecture : Prop :=
  (∀ k : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
    ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m') ∧
  (∀ k g : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
    g ≤ G.girth ∧
    ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m')

/--
Resolved false: Resolved false by Bondy and Vince; formalized in Lean where indicated. Source:
J. A. Bondy and A. Vince, Cycles in a graph whose lengths differ by one or two, Journal of Graph
Theory 27 (1998), 11-15,
https://doi.org/10.1002/(SICI)1097-0118(199801)27:1%3C11::AID-JGT3%3E3.0.CO;2-J; Jun Gao, Qingyi
Huo, Chun-Hung Liu, and Jie Ma, A unified proof of conjectures on cycle lengths in graphs,
arXiv:1904.08126v3, https://arxiv.org/abs/1904.08126v3. Moved from
`OpenConjectures/Combinatorics/ErdosProblem751`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ErdosProblem751Wanted
