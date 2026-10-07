/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- K₅-minor branch-set witness (Wagner/Kuratowski forbidden minor for planarity).
Cites stable source https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
def HasK5Minor {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ S : Fin 5 → Set V,
    (∀ i, ∃ x, x ∈ S i) ∧
    Pairwise (fun i j => ∀ x, x ∈ S i → x ∈ S j → False) ∧
    (∀ i, ∀ u ∈ S i, ∀ v ∈ S i, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ S i) ∧
    ∀ i j, i ≠ j → ∃ u ∈ S i, ∃ v ∈ S j, G.Adj u v

/-- K₃,₃-minor branch-set witness (Wagner/Kuratowski forbidden minor for planarity).
Cites stable source https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
def HasK33Minor {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ L R : Fin 3 → Set V,
    (∀ i, ∃ x, x ∈ L i) ∧
    (∀ j, ∃ x, x ∈ R j) ∧
    (∀ i j, ∀ x, x ∈ L i → x ∈ R j → False) ∧
    Pairwise (fun i i' => ∀ x, x ∈ L i → x ∈ L i' → False) ∧
    Pairwise (fun j j' => ∀ x, x ∈ R j → x ∈ R j' → False) ∧
    (∀ i, ∀ u ∈ L i, ∀ v ∈ L i, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ L i) ∧
    (∀ j, ∀ u ∈ R j, ∀ v ∈ R j, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ R j) ∧
    ∀ i j, ∃ u ∈ L i, ∃ v ∈ R j, G.Adj u v

/-- Planarity as the absence of K₅ and K₃,₃ minors (forbidden-minor condition
constraining to planar embeddable maps; arbitrary finite simple graphs are not
4-colorable, with K₅ as the counterexample).
Cites stable source https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1);
constrains the theorem to planar (embeddable) maps. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ HasK5Minor G ∧ ¬ HasK33Minor G

/-- Four color theorem: no more than four colors are required to color the regions of any
planar map so that no two adjacent regions share a color, where adjacent regions share a
common boundary segment of non-zero length (modeled by `boundaryLength`: adjacency holds
iff the regions are distinct and their shared-boundary length is positive, so corner-only
point contact, of length zero, is excluded). The graph is constrained to planar maps via
`IsPlanar`; without planarity the conclusion is false (K₅ is a counterexample).
Cites stable source https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1). -/
theorem_wanted fourColorTheorem {V : Type} [Fintype V] (G : SimpleGraph V)
    (planar : IsPlanar G)
    (boundaryLength : V → V → ℕ)
    (adj : ∀ u v, G.Adj u v ↔ u ≠ v ∧ 0 < boundaryLength u v) :
    G.Colorable 4

end

end MetaMathlibExt