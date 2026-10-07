/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Geometry.HyperplaneSlicingUniversalWanted

/-!
# Hyperplane slicing conjecture

Formalization of the hyperplane slicing conjecture collected from Oberwolfach Reports.

Source report: Mini-Workshop: Stochastic Analysis for Poisson Point Processes
(2013), Oberwolfach Reports, DOI 10.4171/owr/2013/09, pp. 483--520.
Stable identifier: [OWR-12337-001].

## Clause list

Every hypothesis, side condition, and quantifier domain in the source:

1. There exists a constant `c : ℝ` (one shared universal witness).
2. `0 < c`.
3. For every dimension `n : ℕ` (universal over `n`).
4. `1 ≤ n` (presupposed by "`(n-1)`-dimensional" hyperplane section).
5. For every `K : Set (EuclideanSpace ℝ (Fin n))` (that is, `K ⊆ ℝⁿ`).
6. `K` is convex (`Convex ℝ K`).
7. `K` is compact (`IsCompact K`).
8. `K` has nonempty interior (`Set.Nonempty (interior K)`).
9. `K` has `n`-dimensional Lebesgue volume `1` (`MeasureTheory.volume K = 1`).
10. There exists `H : Set (EuclideanSpace ℝ (Fin n))` (hyperplane).
11. `H` is a hyperplane (`∃ f t, f ≠ 0 ∧ H = {x | f x = t}` for a linear functional `f`).
12. The section is `K ∩ H`.
13. There exists an isometry `φ : EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n)`
    with `Isometry φ` and `Set.range φ = H`, identifying `H` with `ℝⁿ⁻¹`.
14. The `(n-1)`-dimensional volume of `K ∩ H`, measured as
    `MeasureTheory.volume (Set.preimage φ (K ∩ H))`, is at least `c`
    (`ENNReal.ofReal c ≤ ...`).
-/

/-- Convex body in `ℝⁿ`: a convex, compact set with nonempty interior.

Cites [OWR-12337-001] (DOI 10.4171/owr/2013/09): "convex body `K ⊆ ℝⁿ`". -/
def IsConvexBody (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ Set.Nonempty (interior K)

/-- Hyperplane in `ℝⁿ`: a level set `{x | f x = t}` of a nonzero linear functional `f`.

Cites [OWR-12337-001] (DOI 10.4171/owr/2013/09): "hyperplane section". -/
def IsHyperplane (n : ℕ) (H : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (f : LinearMap (RingHom.id ℝ) (EuclideanSpace ℝ (Fin n)) ℝ) (t : ℝ), f ≠ 0 ∧
    H = {x : EuclideanSpace ℝ (Fin n) | f x = t}

/-- Hyperplane slicing conjecture: there exists a universal constant `c > 0` such that
every volume-one convex body in `ℝⁿ` has a hyperplane section of `(n-1)`-volume at
least `c`, where `(n-1)`-volume is Lebesgue volume after identifying the hyperplane
with `ℝⁿ⁻¹` via an isometry.

Cites [OWR-12337-001] (DOI 10.4171/owr/2013/09), where it is posed as an open
problem; it has since been resolved (see the entry metadata). Stated as a
proposition with no proof in this repository. -/
def conjecture : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
        IsConvexBody n K →
          MeasureTheory.volume K = 1 →
            ∃ (H : Set (EuclideanSpace ℝ (Fin n))),
              IsHyperplane n H ∧
                ∃ (φ : EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n)),
                  Isometry φ ∧ Set.range φ = H ∧
                    ENNReal.ofReal c ≤ MeasureTheory.volume (Set.preimage φ (K ∩ H))

/--
Resolved true: Klartag and Lehec (Geom. Funct. Anal. 2025, arXiv:2412.15044), building on Guan's
bound, proved Bourgain's slicing conjecture: every volume-one convex body in R^n has a
hyperplane section of (n-1)-volume greater than a universal c > 0 (Theorem 1.1), equivalently
sup_n L_n < infinity. Source: B. Klartag, J. Lehec, Affirmative resolution of Bourgain's slicing
problem using Guan's bound, Geometric and Functional Analysis (2025), arXiv:2412.15044,
https://arxiv.org/abs/2412.15044. Moved from
`OpenConjectures/Geometry/HyperplaneSlicingUniversal`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.HyperplaneSlicingUniversalWanted
