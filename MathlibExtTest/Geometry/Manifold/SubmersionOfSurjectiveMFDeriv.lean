/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv

@[expose] public section

open scoped ContDiff Manifold Topology
open MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted

namespace MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv

-- The public criterion proves multiplication is a smooth submersion at (1, 0).
example : Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
    (fun p : ℝ × ℝ ↦ p.1 * p.2) (1, 0) := by
  apply Manifold.IsSubmersionAt.of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ ↦ p.1 * p.2) y by
      fun_prop).contMDiffAt
  · have hderiv : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 * p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) := by
      have h :=
        (hasFDerivAt_fst (𝕜 := ℝ) (p := ((1, 0) : ℝ × ℝ))).mul
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((1, 0) : ℝ × ℝ)))
      convert h using 1
      simp
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    intro y
    exact ⟨(0, y), rfl⟩

-- The frozen theorem applies to a nonlinear map whose derivative at the origin is projection.
example : Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
    (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2) (0, 0) := by
  apply submersionAt_of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2) y by
      fun_prop).contMDiffAt
  · have hderiv : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
      have h :=
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ))).pow 2).add
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ)))
      convert h using 1
      simp
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    intro y
    exact ⟨(0, y), rfl⟩

-- Away from zero, the squared norm has nonzero differential and is a smooth submersion.
theorem sqNorm_isSubmersionAt (p₀ : ℝ × ℝ × ℝ) (hp₀ : p₀ ≠ 0) :
    Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
      (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p₀ := by
  apply submersionAt_of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω)
        (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) y by
      fun_prop).contMDiffAt
  · let A : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
      ((2 * p₀.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
        (2 * p₀.2.1) •
          (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
        (2 * p₀.2.2) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    have h :=
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).pow 2).add
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀.2)).comp p₀
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))).pow 2)).add
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p₀.2)).comp p₀
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))).pow 2)
    have hderiv : HasFDerivAt
        (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) A p₀ := by
      convert h using 1
      · funext p
        rfl
      · simp [A, Function.comp_apply]
    have hA (v : ℝ × ℝ × ℝ) :
        A v = 2 * (p₀.1 * v.1 + p₀.2.1 * v.2.1 + p₀.2.2 * v.2.2) := by
      simp [A]
      ring
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    change Function.Surjective A
    intro y
    by_cases h₁ : p₀.1 = 0
    · by_cases h₂ : p₀.2.1 = 0
      · have h₃ : p₀.2.2 ≠ 0 := by
          intro h₃
          exact hp₀ (Prod.ext h₁ (Prod.ext h₂ h₃))
        refine ⟨(0, 0, y / (2 * p₀.2.2)), ?_⟩
        rw [hA]
        field_simp
        ring
      · refine ⟨(0, y / (2 * p₀.2.1), 0), ?_⟩
        rw [hA]
        field_simp
        ring
    · refine ⟨(y / (2 * p₀.1), 0, 0), ?_⟩
      rw [hA]
      field_simp
      ring

-- Openness makes the squared norm a submersion throughout a neighbourhood of p₀.
example (p₀ : ℝ × ℝ × ℝ) (hp₀ : p₀ ≠ 0) :
    ∀ᶠ p in 𝓝 p₀,
      Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
        (fun q : ℝ × ℝ × ℝ ↦ q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2) p := by
  exact isOpen_isSubmersionAt.mem_nhds (sqNorm_isSubmersionAt p₀ hp₀)

end MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv
