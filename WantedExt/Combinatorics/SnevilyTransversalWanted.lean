/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OPG-655 (Snevily's conjecture): let `G` be an abelian group of odd order
and `A B ⊆ G` with `|A| = |B| = k`. Then `A` and `B` can be ordered so
that the `k` sums `aᵢ + bᵢ` are pairwise distinct.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MathlibExt.Combinatorics.SnevilyTransversalWanted

/-! Source record `OPG-655`. -/

/-- [OPG-655] Snevily's conjecture: in an abelian group of odd order, any
two equally sized finite subsets can be paired so the sums are distinct.

The orderings `aᵢ`, `bᵢ` with pairwise distinct sums `aᵢ + bᵢ` are rendered
as a bijection `f : A → B` such that `a ↦ a + f a` is injective: given the
orderings, `f` maps the `i`-th element of `A` to the `i`-th element of `B`,
and conversely any bijection `f` yields orderings by enumerating `A` and
transporting along `f`. -/
def conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Odd (Fintype.card G) →
      ∀ A B : Finset G, A.card = B.card →
        ∃ f : ↥A → ↥B, Function.Bijective f ∧
          ∀ a₁ a₂ : ↥A,
            (a₁ : G) + (f a₁ : G) = (a₂ : G) + (f a₂ : G) → a₁ = a₂

/--
Resolved true: Snevily's conjecture for odd-order abelian groups was proved by Boris Arsovski,
'A proof of Snevily's conjecture', Israel Journal of Mathematics 182 (2011), 505-508. Source:
Boris Arsovski, A proof of Snevily's conjecture, Israel J. Math. 182 (2011), 505-508. Moved from
`OpenConjectures/Combinatorics/SnevilyTransversal`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.SnevilyTransversalWanted
