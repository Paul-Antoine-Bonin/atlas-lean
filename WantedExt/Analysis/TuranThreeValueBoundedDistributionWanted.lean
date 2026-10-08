/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted

/-!
# Hayman Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028]

Stable source: Hayman - Research Problems in Function Theory (2018), Problem 2.28,
source URL `https://arxiv.org/abs/1809.07200`, extraction `source-tex`.

## Clause list from the source (enumeration before formalization)

1. `f` is meromorphic in the plane (domain `ℂ`, `MeromorphicOn f Set.univ`).
2. Quantifier: for every positive `r : ℝ`, `r > 0`.
3. There exists a fixed constant `C(r) : ℕ` depending only on `r`
   (not on the disc centre nor on `w`).
4. Equation `f(z) = w` for arbitrary value `w`, finite or infinite in the
   source. Finite roots are counted with multiplicity via
   `meromorphicOrderAt (fun z => f z - w) z`, not via the raw fibre
   `f ⁻¹' {w}`: the point value of a meromorphic function at a pole or
   removable singularity is not intrinsic, and changing values on a
   locally finite set must not create roots. The value `∞` is counted by
   pole multiplicity (the negative part of `meromorphicOrderAt f z`).
   Values are modeled by `Option ℂ` with `none` for `∞`.
5. In any disc of radius `r` (formalized as `Metric.ball c r` for arbitrary
   centre `c : ℂ`).
6. Never more than `C(r)` roots in such a disc, counted with multiplicity
   (formalized as: for every `Finset ℂ` contained in the disc, the sum of
   root multiplicities is `≤ C`).
7. `f` is nonconstant as a meromorphic germ: for every value `w` there is
   a point at which `f` is not locally identically `w`
   (`meromorphicOrderAt (f - w) z ≠ ⊤`). A pointwise condition would not
   suffice: changing one value of the zero function leaves it meromorphic
   and pointwise nonconstant while its germ is constant. The source
   problem concerns nonconstant meromorphic functions; without this, a
   constant `f` satisfies the three-value bound (three values have empty
   root sets) while failing bounded value distribution at its own value.
8. Context only (not a formal target): it suffices to assume the bound for
   a single value of `r`.
9. Context only (not a formal target): if `f` is entire then `C(r) = O(r)`
   as `r → ∞`, hence at most exponential type.
10. Context only (not a formal target): Wittich's theorem on
    `y⁽ⁿ⁾ + f₁(z)y⁽ⁿ⁻¹⁾ + ⋯ + fₙ(z)y = 0` with entire coefficients having only
    b.v.d. solutions implies the `f_ν` are constants, and conversely.
11. Question hypothesis (P. Turán): the basic bound is assumed for only three
    values `w₁, w₂, w₃ : ℂ`, pairwise distinct.
12. Question claim: does the three-value bound imply `f` is of bounded value
    distribution for all `w`?

Clauses 1–6 are formalized in `IsBoundedValueDistribution`.
Clauses 11–12 are formalized in `conjecture`.
Clauses 8–10 are recorded here as context evidence and are not separate targets.
-/

/-- Multiplicity of `z` as a root of the equation `f (·) = w`: the
meromorphic order of `f - w` at `z`, read as an extended natural number.
This is `0` at non-roots and at poles, is unchanged when values of `f`
are altered at isolated points, and is `⊤` when `f` is identically `w`
on a punctured neighbourhood of `z` (infinitely many roots, not zero).

Citing stable source identifiers: Hayman - Research Problems in Function Theory
(2018), Problem 2.28 [AMR-022-2028], `https://arxiv.org/abs/1809.07200`. -/
noncomputable def rootMult (f : ℂ → ℂ) (w z : ℂ) : ℕ∞ :=
  if meromorphicOrderAt (fun t => f t - w) z = ⊤ then ⊤
  else ((meromorphicOrderAt (fun t => f t - w) z).untopD 0).toNat

/-- Multiplicity of `z` as a pole of `f`, i.e. the multiplicity of the
value `∞` at `z`: the negative part of the meromorphic order of `f` at
`z`. This is `0` unless `f` genuinely has a pole at `z`.

Citing stable source identifiers: Hayman - Research Problems in Function Theory
(2018), Problem 2.28 [AMR-022-2028], `https://arxiv.org/abs/1809.07200`. -/
noncomputable def poleMult (f : ℂ → ℂ) (z : ℂ) : ℕ∞ :=
  ((-(meromorphicOrderAt f z).untopD 0).toNat : ℕ∞)

/-- Multiplicity of `z` as a preimage of the value `w` on the Riemann
sphere: finite values `some w` are counted by `rootMult`, and the value
at infinity `none` is counted by pole multiplicity `poleMult`.

Citing stable source identifiers: Hayman - Research Problems in Function Theory
(2018), Problem 2.28 [AMR-022-2028], `https://arxiv.org/abs/1809.07200`. -/
noncomputable def rootMultSph (f : ℂ → ℂ) (w : Option ℂ) (z : ℂ) : ℕ∞ :=
  match w with
  | some w => rootMult f w z
  | none => poleMult f z

/-- Bounded value distribution for a plane meromorphic function.

Citing stable source identifiers: Hayman - Research Problems in Function Theory
(2018), Problem 2.28 [AMR-022-2028], `https://arxiv.org/abs/1809.07200`:
for every positive `r` there exists `C(r)` such that `f(z) = w` has at most
`C(r)` roots, counted with multiplicity, in any disc of radius `r`, for
every value `w` finite or infinite (poles counted with multiplicity). -/
def IsBoundedValueDistribution (f : ℂ → ℂ) : Prop :=
  ∀ (r : ℝ), r > 0 →
    ∃ C : ℕ, ∀ (c : ℂ) (w : Option ℂ) (s : Finset ℂ),
      (↑s ⊆ Metric.ball c r) → ∑ z ∈ s, rootMultSph f w z ≤ (C : ℕ∞)

/-- Turán's three-value question for b.v.d. functions.

Citing stable source identifiers: Hayman - Research Problems in Function Theory
(2018), Problem 2.28 [AMR-022-2028], `https://arxiv.org/abs/1809.07200`,
question by P. Turán: is the basic bounded-roots assumption for only three
values `w₁, w₂, w₃` sufficient to assure a nonconstant meromorphic `f` is
of b.v.d. for all values? Stated as the implication from the three-value
bound to `IsBoundedValueDistribution`. -/
def conjecture : Prop :=
  ∀ (f : ℂ → ℂ), MeromorphicOn f Set.univ →
    (∀ w : ℂ, ∃ z : ℂ, meromorphicOrderAt (fun t => f t - w) z ≠ ⊤) →
    (∃ w₁ w₂ w₃ : Option ℂ, w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
      ∀ (r : ℝ), r > 0 →
        ∃ C : ℕ, ∀ (c : ℂ) (w : Option ℂ), w ∈ ({w₁, w₂, w₃} : Set (Option ℂ)) →
          ∀ (s : Finset ℂ),
            (↑s ⊆ Metric.ball c r) → ∑ z ∈ s, rootMultSph f w z ≤ (C : ℕ∞)) →
    IsBoundedValueDistribution f
/--
Resolved false: A. A. Gol'dberg (Izv. Vyssh. Uchebn. Zaved. Mat. 1972) answered Turan's question
negatively, as recorded in Hayman-Lingham Update 2.28; the Weierstrass sigma-function is another
counterexample: it has boundedly many w-points per disc for every bounded set of w but has order
2, so it is not b.v.d. Source: W. K. Hayman and E. F. Lingham, Research Problems in Function
Theory (2018), arXiv:1809.07200, https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/TuranThreeValueBoundedDistribution`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted
