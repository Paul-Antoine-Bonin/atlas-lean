/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Homomesy of antichain cardinality under type-A rowmotion
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Antichain

@[expose] public section

namespace MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted

/-! Source record `AIM-OTHER-0019__20003212`. -/

/-!
# AIM-OTHER-0019: Type-A antichain rowmotion homomesy

Conjecture 3.3 from aim-other-notes.json notes[18]
(AIM Problem Lists, Dynamical algebraic combinatorics,
http://aimath.org/pastworkshops/dac_preworkshop.pdf).

Clause list for the formalized claim (Conjecture 3.3 only; birational remarks
for n ≤ 3 and Theorem 3.4 are context evidence, not additional targets):
- (n : ℕ): index of the type-A root poset; no lower-bound exclusion in source.
- (P : Type*) [PartialOrder P] [Finite P]: finite poset domain.
- IsTypeARootPoset P n: P is order-isomorphic to triangular pairs
  {(i,j) : Fin n × Fin n // i ≤ j} with interval-inclusion order
  (a ≤ b ↔ b.1 ≤ a.1 ∧ a.2 ≤ b.2).
- PosetAntichain P: antichains of P as Finsets satisfying IsAntichain (· ≤ ·).
- rhoPrime : PosetAntichain P → PosetAntichain P: antichain rowmotion;
  bijective with defining equation x ∈ rhoPrime(A) ↔ x minimal in complement
  of down-set of A.
- f : PosetAntichain P → ℚ: antichain-cardinality statistic; f(A) = |A|.
- IsHomomesic rhoPrime f c: Finite domain, bijective action, and one shared
  orbit-average c for every x and every period k > 0 with iterate k x = x.
- c = (n : ℚ) / 2: exact average value n/2.
-/

open scoped BigOperators

/-- Homomesy with one shared orbit-average `c` under iteration of `σ`.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsHomomesic {α : Type*} (σ : α → α) (f : α → ℚ) (c : ℚ) : Prop :=
  Finite α ∧
  Function.Bijective σ ∧
  ∀ (x : α) (k : ℕ), 0 < k → Nat.iterate σ k x = x →
    (Finset.sum (Finset.range k) (fun i => f (Nat.iterate σ i x))) / (k : ℚ) = c

/-- Antichains of a poset as `Finset`s satisfying `IsAntichain`.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def PosetAntichain (P : Type*) [PartialOrder P] :=
  { s : Finset P // IsAntichain (· ≤ ·) (s : Set P) }

/-- Antichain-cardinality statistic: `f A = |A|` as a rational.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainCardinality (P : Type*) [PartialOrder P]
    (f : PosetAntichain P → ℚ) : Prop :=
  ∀ A : PosetAntichain P, f A = (A.val.card : ℚ)

/-- Antichain rowmotion: bijective map sending `A` to minima of complement of its down-set.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainRowmotion (P : Type*) [PartialOrder P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) : Prop :=
  Function.Bijective rhoPrime ∧
  ∀ (A : PosetAntichain P) (x : P),
    x ∈ (rhoPrime A).val ↔
      ((¬ ∃ a ∈ A.val, x ≤ a) ∧
        ∀ (y : P), (¬ ∃ a ∈ A.val, y ≤ a) → y ≤ x → y = x)

/-- Type-A root poset: order-isomorphic to triangular intervals with inclusion order.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsTypeARootPoset (P : Type*) [PartialOrder P] (n : ℕ) : Prop :=
  ∃ e : P ≃ { p : Fin n × Fin n // p.1 ≤ p.2 },
    ∀ (a b : P), a ≤ b ↔
      ((e b).val.1 ≤ (e a).val.1 ∧ (e a).val.2 ≤ (e b).val.2)

/-- Conjecture 3.3: antichain cardinality is homomesic under rowmotion with average `n/2`.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def conjecture : Prop :=
  ∀ (n : ℕ) (P : Type*) [PartialOrder P] [Finite P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) (f : PosetAntichain P → ℚ),
    IsTypeARootPoset P n →
      IsAntichainRowmotion P rhoPrime →
        IsAntichainCardinality P f →
          IsHomomesic rhoPrime f ((n : ℚ) / 2)

/--
Resolved true: This is the type-A case of Panyushev's antichain-orbit conjecture, proved for all
crystallographic root systems by Armstrong, Stump, and Thomas (Trans. Amer. Math. Soc. 365,
2013); the claim is resolved affirmatively. Source: D. Armstrong, C. Stump, and H. Thomas, A
uniform bijection between nonnesting and noncrossing partitions, Transactions of the American
Mathematical Society 365 (2013). Moved from
`OpenConjectures/Combinatorics/RootPosetRowmotionHomomesy`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted
