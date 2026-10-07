/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 914
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem914Wanted

/-! Source record `FC-ErdosProblem914`, ported from FormalConjectures
`ErdosProblems/914.lean` (`theorem erdos_914`,
`theorem erdos_914.variants.equitable_colouring`) and checked against
erdosproblems.com/914. The two claims are conjoined into one `conjecture`.
Status: resolved true (Corrádi–Hajnal for `r = 3`, Hajnal–Szemerédi for
`r ≥ 4`); the registry links a proof-bearing external Lean development. -/

/-- The Corrádi–Hajnal / Hajnal–Szemerédi `K_r`-factor claim and its
equitable-colouring reformulation, conjoined. -/
def conjecture : Prop :=
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → m * (r - 1) ≤ G.minDegree →
    ∃ K : Fin m → Finset V, (∀ i, G.IsNClique r (K i)) ∧
      Pairwise fun i j => Disjoint (K i) (K j)) ∧
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → G.maxDegree ≤ m - 1 →
    ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r)

/--
Resolved true: Proved by Corrádi–Hajnal and Hajnal–Szemerédi; a proof is available in an
external Lean development. Source: A. Hajnal and E. Szemerédi, Proof of a conjecture of P. Erdős
(1970), 601–623, https://mathscinet.ams.org/mathscinet-getitem?mr=297607; External Lean proof of
Erdős Problem 914, plby/lean-proofs at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos914.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem914`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem914Wanted
