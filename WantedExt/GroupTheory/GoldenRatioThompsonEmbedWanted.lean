/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-16167-018: Does Cleary's golden-ratio Thompson group F_tau embed
in Thompson's group F? (The poset-structure question is not
formalized.)
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.GoldenRatioThompsonEmbedWanted

/-! Source record `OWR-16167-018`. Following Hyde and Moore (arXiv:2103.14911, Section 7), both
groups are subgroups of `PL₊(I)`: orientation-preserving piecewise-linear homeomorphisms of
`I = [0, 1]` with finitely many breakpoints, viewed as permutations of `ℝ` that are the identity
outside `I`. -/

/-- `x` lies in `ℤ[1/2]`. -/
def IsDyadic (x : ℝ) : Prop :=
  ∃ (a : ℤ) (n : ℕ), x = a / 2 ^ n

/-- `x` lies in `ℤ[τ]`, where `τ` is the golden ratio (`τ ^ 2 = τ + 1`, `τ > 1`). -/
def IsGoldenInteger (x : ℝ) : Prop :=
  ∃ a b : ℤ, x = a + b * Real.goldenRatio

/-- `f` is the identity outside `[0, 1]` and, on `[0, 1]`, is affine on each piece of a finite
subdivision `0 = t₀ < ⋯ < tₙ₊₁ = 1` whose points lie in `B`, with every slope in `S`. Adjacent
pieces agree at the shared point, so `f` restricts to a piecewise-linear homeomorphism of
`[0, 1]` when the slopes are positive. -/
def IsPLHomeoWith (B S : Set ℝ) (f : Equiv.Perm ℝ) : Prop :=
  (∀ x, x ∉ Set.Icc (0 : ℝ) 1 → f x = x) ∧
    ∃ (n : ℕ) (t : Fin (n + 2) → ℝ), StrictMono t ∧ t 0 = 0 ∧ t (Fin.last _) = 1 ∧
      (∀ i, t i ∈ B) ∧
      ∀ i : Fin (n + 1), ∃ s ∈ S, ∀ x ∈ Set.Icc (t i.castSucc) (t i.succ),
        f x = f (t i.castSucc) + s * (x - t i.castSucc)

/-- Thompson's group `F`: breakpoints in `ℤ[1/2]`, slopes powers of `2`. -/
def thompsonF : Set (Equiv.Perm ℝ) :=
  {f | IsPLHomeoWith {x | IsDyadic x} (Set.range fun k : ℤ => (2 : ℝ) ^ k) f}

/-- Cleary's golden-ratio Thompson group `F_τ`: breakpoints in `ℤ[τ]`, slopes powers of `τ`. -/
def clearyFTau : Set (Equiv.Perm ℝ) :=
  {f | IsPLHomeoWith {x | IsGoldenInteger x} (Set.range fun k : ℤ => Real.goldenRatio ^ k) f}

/-- [OWR-16167-018] `F_τ` embeds in `F`: some map sends `F_τ` injectively into `F` and is
multiplicative on `F_τ`. Since `F_τ` is a group under composition, this is an injective group
homomorphism `F_τ → F`. -/
def conjecture : Prop :=
  ∃ φ : Equiv.Perm ℝ → Equiv.Perm ℝ, (∀ g ∈ clearyFTau, φ g ∈ thompsonF) ∧
    Set.InjOn φ clearyFTau ∧ ∀ g ∈ clearyFTau, ∀ h ∈ clearyFTau, φ (g * h) = φ g * φ h

/--
Resolved false: Hyde and Moore (Groups Geom. Dyn. 17 (2023) 533-554, arXiv:2103.14911)
introduced F-obstructions and proved that Cleary's golden-ratio group F_tau does not embed into
Thompson's group F (Corollary 1.4; Corollary 1 in arXiv v1). Source: J. Hyde, J. T. Moore,
Subgroups of PL+I which do not embed into Thompson's group F, Groups, Geometry, and Dynamics 17
(2023) 533-554, arXiv:2103.14911, https://arxiv.org/abs/2103.14911. Moved from
`OpenConjectures/GroupTheory/GoldenRatioThompsonEmbed`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.GoldenRatioThompsonEmbedWanted
