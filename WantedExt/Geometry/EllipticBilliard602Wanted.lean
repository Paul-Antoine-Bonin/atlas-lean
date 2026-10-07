/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elliptic-billiard invariant k_{602}
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

namespace MathlibExt.Geometry.EllipticBilliard602Wanted

/-! Source record `AMR-050-0031__5100031`. -/

open scoped BigOperators

/-!
# Elliptic-billiard invariant k₆₀₂ — clause inventory

Source: [AMR-050-0031] Reznik, Garcia, and Koiller,
Eighty New Invariants of N-Periodics in the Elliptic Billiard (2021),
Table row k₆₀₂, https://arxiv.org/abs/2004.12497, accessed 2026-07-29,
extraction source-tex, difficulty L3, status NEEDS_REVIEW (presented as open).

Clause list from the source:
(a) fixed outer ellipse in `EuclideanSpace ℝ (Fin 2)`:
  `dist X f₁ + dist X f₂ = a` with `dist f₁ f₂ < a`;
(b) center `O` with focus-center relation `O = (1 / 2 : ℝ) • (f₁ + f₂)`;
(c) foci `f₁ f₂` of that ellipse;
(d) fixed confocal caustic with the same foci and parameter `ac`,
  `dist f₁ f₂ < ac` and `ac < a`;
(e) `N`-periodic orbits `P : ℕ → EuclideanSpace ℝ (Fin 2)` with
  `P (i + N) = P i`, every `P i` on the outer ellipse,
  consecutive vertices distinct;
(f) billiard / Poncelet closure encoded in Mathlib-grounded form as
  inscription plus confocal tangency: each sideline through
  `P i.val`, `P (i.val + 1)` meets the caustic in exactly one point
  (`∃!`), by the Poncelet porism;
(g) `P` ranges over the full predicate-defined family
  (`∀ P` satisfying (e)–(f)), not a caller-chosen set;
(h) pedal data: `Q₁ Q₂ : Fin N → EuclideanSpace ℝ (Fin 2)` with each
  `Qⱼ i` on sideline `i` and closest to `fⱼ`, and
  `q_{j,i} = dist fⱼ (Qⱼ i)` (foot-of-perpendicular via closest point,
  using only `dist` and affine lines);
(i) universal quantification over all `N` with no threshold or exception;
(j) constancy with one shared witness `C`, not independent existentials:
  `∃ C ∀ P Q₁ Q₂, … → (∏ i q_{1,i}) * (∏ i q_{2,i}) = C`;
(k) context only, no Mathlib counterpart, omitted from binders since the
  claimed constancy does not use them: outer polygon `P'`, inner polygon
  `P''`, areas `A, A', A''`, antipedal distances `q^*_{j,i}`, pedal areas
  and starred antipedal areas;
(l) source label `k₆₀₂`; the source's item stated as a closed proposition,
  with no proof in this repository.

Recovery grounding: all binders use existing Mathlib notions
(`EuclideanSpace`, `dist`, `•`, `Fin`, `Finset.prod`); no new structure
is introduced and source concepts without a counterpart are carried by
the closest formulation above.
-/

/-- Invariant k₆₀₂ from [AMR-050-0031] (Reznik–Garcia–Koiller 2021, Table row
k₆₀₂, arXiv:2004.12497): for every `N`, with outer ellipse
`dist X f₁ + dist X f₂ = a`, center `O = (1 / 2 : ℝ) • (f₁ + f₂)`,
`dist f₁ f₂ < a`, and confocal caustic `dist f₁ f₂ < ac < a`, there is one
shared `C` such that every `N`-periodic Poncelet orbit `P` (on-ellipse,
`N`-periodic, distinct consecutive vertices, each sideline uniquely meeting
the caustic) with pedal feet `Q₁ Q₂` (on-sideline closest points to
`f₁ f₂`) satisfies
`(∏ i : Fin N, dist f₁ (Q₁ i)) * (∏ i : Fin N, dist f₂ (Q₂ i)) = C`.
`P'`, `P''`, areas, and antipedal data are source context only and do not
enter the binders. As the source presents the item as open, this states the
question as a proposition. -/
def conjecture : Prop :=
  ∀ (N : ℕ) (O f₁ f₂ : EuclideanSpace ℝ (Fin 2)) (a ac : ℝ),
    O = ((1 / 2 : ℝ) • (f₁ + f₂)) →
    dist f₁ f₂ < a →
    dist f₁ f₂ < ac →
    ac < a →
    ∃ C : ℝ,
      ∀ (P : ℕ → EuclideanSpace ℝ (Fin 2)) (Q₁ Q₂ : Fin N → EuclideanSpace ℝ (Fin 2)),
        (∀ i, dist (P i) f₁ + dist (P i) f₂ = a) →
        (∀ i, P (i + N) = P i) →
        (∀ i : Fin N, P i.val ≠ P (i.val + 1)) →
        (∀ i : Fin N, ∃! X : EuclideanSpace ℝ (Fin 2),
          (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) ∧
            dist X f₁ + dist X f₂ = ac) →
        (∀ i : Fin N, (∃ t : ℝ, Q₁ i = P i.val + t • (P (i.val + 1) - P i.val)) ∧
          ∀ X : EuclideanSpace ℝ (Fin 2),
            (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) →
              dist f₁ (Q₁ i) ≤ dist f₁ X) →
        (∀ i : Fin N, (∃ t : ℝ, Q₂ i = P i.val + t • (P (i.val + 1) - P i.val)) ∧
          ∀ X : EuclideanSpace ℝ (Fin 2),
            (∃ t : ℝ, X = P i.val + t • (P (i.val + 1) - P i.val)) →
              dist f₂ (Q₂ i) ≤ dist f₂ X) →
        (∏ i : Fin N, dist f₁ (Q₁ i)) * (∏ i : Fin N, dist f₂ (Q₂ i)) = C

/--
Resolved true: Bialy and Tabachnikov (Dan Reznik's identities and more, Eur. J. Math. 2020,
arXiv:2001.08469), Lemma 4.2: for each side tangent to the confocal caustic with semi-minor axis
b, the two focal distances multiply to b^2. Multiplying over the N sides gives the invariant
k602 = b^(2N) for every N. Source: M. Bialy, S. Tabachnikov, Dan Reznik's identities and more,
European Journal of Mathematics (2020), arXiv:2001.08469, https://arxiv.org/abs/2001.08469.
Moved from `OpenConjectures/Geometry/EllipticBilliard602`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.EllipticBilliard602Wanted
