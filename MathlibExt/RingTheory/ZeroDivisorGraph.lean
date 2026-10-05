-- MathlibExt/RingTheory/ZeroDivisorGraph.lean
module
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Combinatorics.SimpleGraph.Basic
/-!
# Zero-divisor graph of a commutative ring

Formalizes the zero-divisor graph from Marco Caoduro and Meike Neuwohner,
[Boxicity and Threshold Dimension of Zero Divisor Graphs](https://arxiv.org/abs/2608.27381v1)
(formalized definition in `boxicity_arxiv.tex` lines 383–390):
vertices are the nonzero zero divisors and two vertices are
adjacent exactly when their product is zero.

The cited paper studies finite nonzero (commutative unital) rings,
while the reusable definition here works generally for any
commutative ring: the construction and proofs below require only
`CommRing R`, with no `Nontrivial R` or `Fintype R` hypotheses.
-/
universe u

@[expose] public section

namespace ZeroDivisorGraph

/-- Vertices are nonzero zero divisors, as a subtype of the ring. -/
public abbrev Vertex (R : Type u) [CommRing R] :
    Type u := { r : R // r ≠ 0 ∧ r ∉ nonZeroDivisors R }

/-- Zero-divisor graph via the zero-product relation. -/
public def zeroDivisorGraph (R : Type u) [CommRing R] :
    SimpleGraph (Vertex R) :=
  SimpleGraph.fromRel fun v w : Vertex R => (v : R) * (w : R) = 0

/-- An element lifts to a vertex iff it is nonzero and a zero divisor. -/
public theorem exists_vertex_iff (R : Type u) [CommRing R] (r : R) :
    (∃ v : Vertex R, (v : R) = r) ↔ (r ≠ 0 ∧ r ∉ nonZeroDivisors R) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · rintro ⟨h0, hmem⟩
    exact ⟨⟨r, h0, hmem⟩, rfl⟩

/-- Adjacency is distinctness plus zero product in source orientation. -/
public theorem adj_iff (R : Type u) [CommRing R]
    {v w : Vertex R} :
    (zeroDivisorGraph R).Adj v w ↔ v ≠ w ∧ (v : R) * (w : R) = 0 := by
  unfold zeroDivisorGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [mul_comm]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

end ZeroDivisorGraph
