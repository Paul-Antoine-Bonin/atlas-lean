/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.EdgeIndexedMultigraph

import Mathlib.Tactic.FinCases

@[expose] public section

open scoped BigOperators

namespace MathlibExtTest.EdgeIndexedMultigraph

open SimpleGraph

def single : EdgeIndexedMultigraph (Fin 2) Unit where
  ends _ := s(0, 1)
  loopless := by
    intro _ v
    fin_cases v <;> decide

def double : EdgeIndexedMultigraph (Fin 2) (Unit ⊕ Unit) :=
  single.disjointSum single

example : double.ends (Sum.inl ()) = double.ends (Sum.inr ()) := by
  rw [double, SimpleGraph.EdgeIndexedMultigraph.disjointSum_ends_inl,
    SimpleGraph.EdgeIndexedMultigraph.disjointSum_ends_inr]

private theorem first_ends : double.ends (Sum.inl ()) = s(0, 1) :=
  rfl

private theorem second_ends : double.ends (Sum.inr ()) = s(1, 0) := by
  rw [Sym2.eq_swap]
  rfl

private def circuitTail : double.IndexedWalk 1 0 :=
  .cons (Sum.inr ()) second_ends (.nil 0)

private def circuit : double.IndexedWalk 0 0 :=
  .cons (Sum.inl ()) first_ends circuitTail

private theorem circuit_support : circuit.support = [0, 1, 0] := by
  calc
    circuit.support = 0 :: circuitTail.support :=
      SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_cons
        double (Sum.inl ()) first_ends circuitTail
    _ = 0 :: 1 :: (SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.nil 0 :
      double.IndexedWalk 0 0).support := by
        rw [circuitTail,
          SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_cons]
    _ = [0, 1, 0] := by
      rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_nil]

private theorem circuit_edges : circuit.edges = [Sum.inl (), Sum.inr ()] := by
  calc
    circuit.edges = Sum.inl () :: circuitTail.edges :=
      SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_cons
        double (Sum.inl ()) first_ends circuitTail
    _ = Sum.inl () :: Sum.inr () ::
        (SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.nil 0 :
          double.IndexedWalk 0 0).edges := by
      rw [circuitTail, SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_cons]
    _ = [Sum.inl (), Sum.inr ()] := by
      rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_nil]

example : circuit.support = [0, 1, 0] ∧
    circuit.edges = [Sum.inl (), Sum.inr ()] := by
  exact ⟨circuit_support, circuit_edges⟩

example : circuit.IsTrail := by
  rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.isTrail_iff, circuit_edges]
  decide

example : circuit.IsEulerian := by
  rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.isEulerian_iff]
  constructor
  · rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.isTrail_iff, circuit_edges]
    decide
  · intro e
    rw [circuit_edges]
    cases e <;> simp

example : single.Inc 0 () := by
  rw [SimpleGraph.EdgeIndexedMultigraph.inc_iff]
  simp [single]

example : single.Inc 1 () := by
  rw [SimpleGraph.EdgeIndexedMultigraph.inc_iff]
  simp [single]

private theorem single_underlying : single.underlying = ⊤ := by
  ext u v
  rw [SimpleGraph.EdgeIndexedMultigraph.underlying_adj]
  fin_cases u <;> fin_cases v <;> simp [single, Sym2.eq_swap]

example : single.underlying.Adj 0 1 := by
  rw [single_underlying]
  simp

example : circuit.toWalk.support = [0, 1, 0] ∧
    circuit.toWalk.edges = [s(0, 1), s(0, 1)] ∧
    circuit.toWalk.length = 2 := by
  constructor
  · rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_toWalk]
    exact circuit_support
  constructor
  · rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_toWalk, circuit_edges]
    rfl
  · rw [SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.length_toWalk, circuit_edges]
    rfl

private theorem single_degree (v : Fin 2) : single.degree v = 1 := by
  fin_cases v <;>
    simp [SimpleGraph.EdgeIndexedMultigraph.degree_eq_ncard_inc, single]

example : single.degree 0 = 1 := by
  rw [SimpleGraph.EdgeIndexedMultigraph.degree_eq_ncard_inc]
  simp [single]

private theorem double_degree (v : Fin 2) : double.degree v = 2 := by
  rw [double, SimpleGraph.EdgeIndexedMultigraph.disjointSum_degree,
    single_degree]

private theorem double_connected : double.underlying.Connected := by
  apply SimpleGraph.EdgeIndexedMultigraph.disjointSum_connected_left
  rw [single_underlying]
  exact SimpleGraph.connected_top

example : double.degree 0 = 2 ∧ double.underlying.Reachable 0 1 :=
  ⟨double_degree 0, double_connected 0 1⟩

example : Even (∑ v, double.degree v) :=
  SimpleGraph.EdgeIndexedMultigraph.even_sum_degree double

theorem indexedEulerian_concrete :
    ∃ (u : Fin 2) (p : double.IndexedWalk u u),
    p.IsTrail ∧ Sum.inl () ∈ p.edges ∧ Sum.inr () ∈ p.edges := by
  obtain ⟨u, p, hp⟩ := double.exists_indexedEulerian double_connected (by
    intro v
    rw [double_degree]
    exact even_two)
  exact ⟨u, p, hp.1, hp.2 (Sum.inl ()), hp.2 (Sum.inr ())⟩

example : ∃ (u : Fin 2) (p : double.IndexedWalk u u),
    p.IsTrail ∧ Sum.inl () ∈ p.edges ∧ Sum.inr () ∈ p.edges := by
  have hs : double.underlying.support = Set.univ :=
    double_connected.preconnected.support_eq_univ
  have hsupport :
      (double.underlying.induce double.underlying.support).Connected := by
    rw [hs]
    exact double.underlying.induceUnivIso.connected_iff.mpr double_connected
  obtain ⟨u, p, hp⟩ := double.exists_indexedEulerian_connectedSupport hsupport (by
    intro v
    rw [double_degree]
    exact even_two)
  exact ⟨u, p, hp.1, hp.2 (Sum.inl ()), hp.2 (Sum.inr ())⟩

end MathlibExtTest.EdgeIndexedMultigraph
