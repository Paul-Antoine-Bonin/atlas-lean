module

import MathlibExt.Combinatorics.SimpleGraph.BookNumber

@[expose] public section

namespace SimpleGraph

example {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (h : G.Adj u v) :
    (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ G.bookNumber :=
  le_bookNumber h

example {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (b : ℕ)
    (h : ∀ u v : V, G.Adj u v →
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ b) :
    G.bookNumber ≤ b :=
  bookNumber_le b h

end SimpleGraph

end
