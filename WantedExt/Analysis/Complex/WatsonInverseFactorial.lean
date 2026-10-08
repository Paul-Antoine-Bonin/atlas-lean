/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Watson inverse-factorial expansion (statement only; formal statement recorded here).
Source: https://cs.uwaterloo.ca/journals/JIS/VOL25/Schumacher/schu9.tex, lines 370-417.
Source-file SHA-256: 41dc7a8e6903712c9106e5b139863125b6ce0b5db3b2dd7a7667a5e5182736f3.
Source-text SHA-256: 72031b9f6cb272bda550d3477e59119fbd192f4b8613d31404d26b6d101f86d5.
Stable grounded ID: jis_grounded_89b21b7605c15f787377247f.
Use accounting (corrected): 4 mentions / 1 paper / 1 proof use.
Scope exclusion: excludes the `M = 1, w = 0` specialization and the later Stirling-coefficient
theorem.
-/
theorem_wanted watson_inverse_factorial_series
    (f : ℂ → ℂ) (a : ℕ → ℂ) (R : ℕ → ℂ → ℂ)
    (A B ρ σ γ α δ p M₀ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hγ : 0 ≤ γ) (hα : 0 < α) (hδ : 0 < δ)
    (hangle : α + 3 * δ < Real.pi / 2)
    (hp_lower : 1 < p)
    (hp_upper : p < 1 + Real.exp (-Real.pi * Real.cot α))
    (hanalytic_right : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hanalytic_sector : AnalyticOnNhd ℂ f
      {z : ℂ | γ < ‖z‖ ∧ |Complex.arg z| ≤ Real.pi / 2 + α + 3 * δ})
    (hasymptotic : ∀ n : ℕ, ∀ z : ℂ,
      z ∈ {u : ℂ | γ < ‖u‖ ∧ |Complex.arg u| ≤ Real.pi / 2 + α + 3 * δ} →
      f z = ∑ k ∈ Finset.range (n + 1), a k / z ^ k + R n z)
    (ha_bound : ∀ n : ℕ, ‖a n‖ < A * ρ ^ n * n.factorial)
    (hR_bound : ∀ n : ℕ, ∀ z : ℂ,
      z ∈ {u : ℂ | γ < ‖u‖ ∧ |Complex.arg u| ≤ Real.pi / 2 + α + 3 * δ} →
      ‖R n z * z ^ (n + 1)‖ < B * σ ^ n * n.factorial)
    (hM₀ : IsGreatest
      {x : ℝ | 0 < x ∧
        Real.exp (-(2 * Real.cos α) / (ρ * x)) -
          2 * Real.cos (Real.sin α / (ρ * x)) *
            Real.exp (-Real.cos α / (ρ * x)) + 1 - p ^ 2 = 0} M₀) :
    ∀ M : ℝ, 0 < M → M ≤ M₀ → ∀ w : ℂ, 0 ≤ w.re →
      ∃ b : ℕ → ℂ, ∀ z : ℂ, 0 < z.re →
        Summable (fun k : ℕ =>
          ‖b (k + 1) /
            ∏ j ∈ Finset.range (k + 1),
              ((M : ℂ) * z + w + ((j + 1 : ℕ) : ℂ))‖) ∧
        HasSum
          (fun k : ℕ =>
            b (k + 1) /
              ∏ j ∈ Finset.range (k + 1),
                ((M : ℂ) * z + w + ((j + 1 : ℕ) : ℂ)))
          (f z - b 0)

end

end MetaMathlibExt
