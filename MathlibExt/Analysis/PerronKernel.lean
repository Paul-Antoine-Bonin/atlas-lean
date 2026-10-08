/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectilinearCycle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Order.OrderClosed

/-!
# Truncated Perron kernel

The truncated Perron kernel
`perronKernel y c T = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, i.e.
`(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds` with `ds = i dt`, with the explicit
error bound toward the step function:
`‖K - ind‖ ≤ y^c/(π T |log y|)`. Proved by closing the contour left
(`y > 1`) or right (`y < 1`): the entire averaging operator `E1`
splits off the pole, Cauchy kills the entire part, and the `1/s`
rectangle gives the residue; side estimates plus the `U → ∞` limit
give the bound.

Mathematical and proof source: the Apache-2.0 file
`proofs/Cathedral/White/Infrastructure/PerronKernel.lean` in `jrgochan/prime`,
commit `dd04f61337fb020855c12a97558f66608ab2f969`. The exact source results are
`perron_kernel_gt_one` (lines 703–740), `perron_kernel_lt_one` (lines 845–884),
and the unified `perron_kernel_bound` (lines 894–905); the pinned source file's
SHA-256 is
`a6191587cf9ef800679d06dd7016af6173b30ff19cce866fe707e3b195b64391`.
The contour architecture was adapted from that source. This module is a
substantial original rewrite for MathlibExt; no external Lean source was copied
verbatim. “Schoenfeld shape” in the PR title describes the bound's later
analytic-number-theory use, not a claim that Schoenfeld's paper contains this
exact theorem.
-/

@[expose] public section
namespace PerronKernel

open Complex Filter MeasureTheory Set intervalIntegral
open scoped Topology

/-- Truncated Perron kernel as a real integral over the segment. -/
noncomputable def perronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ in (-T)..T,
    (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)

/-- The kernel integrand is continuous when `0 < y` and `c ≠ 0`. -/
theorem continuous_perronKernel_integrand {y c : ℝ} (hy : 0 < y) (hc : c ≠ 0) :
    Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)) := by
  have hbase : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  have hexp : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hnum : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * Complex.I)) :=
    hexp.const_cpow (Or.inl hbase)
  have hden : ∀ t : ℝ, (c : ℂ) + t * Complex.I ≠ 0 := by
    intro t h
    apply hc
    have := congrArg Complex.re h
    simpa using this
  exact hnum.div hexp hden

/-! The following compatibility lemmas retain the established Perron-kernel
API while delegating the general interval and rectangle calculations to the
neutral complex-analysis layer. -/

open Real in
theorem integral_div_add_sq {d a b : ℝ} (hc : d ≠ 0) :
    ∫ x : ℝ in a..b, d / (x ^ 2 + d ^ 2) = arctan (b / d) - arctan (a / d) :=
  Complex.integral_div_add_sq hc

theorem odd_integral_eq_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (T : ℝ) :
    ∫ x : ℝ in (-T)..T, f x = 0 :=
  Complex.odd_integral_eq_zero hodd T

open Real in
theorem vertical_side_one_div {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) :
    ∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I) = 2 * arctan (T / c) :=
  Complex.vertical_side_one_div hc hT

open Real in
theorem horiz_diff_one_div {a b T : ℝ} (hT : T ≠ 0) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I)) =
        2 * Complex.I * (arctan (b / T) - arctan (a / T)) :=
  Complex.horiz_diff_one_div hT hab

open Real in
theorem boundary_rect_one_div {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I))) =
        2 * Real.pi * Complex.I :=
  Complex.boundary_rect_one_div ha hb hT

open Real in
theorem boundary_rect_one_div_outside {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I))) = 0 :=
  Complex.boundary_rect_one_div_outside ha hab hT

/-- `exp w - 1 = w * ∫_0^1 exp (t * w)`, by FTC. -/
theorem exp_sub_one_eq (w : ℂ) :
    Complex.exp w - 1 = w * ∫ t : ℝ in (0:ℝ)..1, Complex.exp (t * w) := by
  have hF : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t * w))
      (w * Complex.exp (t * w)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      have h := (hasDerivAt_id (t : ℝ)).ofReal_comp.mul_const w
      simpa using h
    have h2 := h1.cexp
    simpa [mul_comm] using h2
  have hderivfun : deriv (fun t : ℝ => Complex.exp (t * w))
      = fun t : ℝ => w * Complex.exp (t * w) :=
    funext fun t => (hF t).deriv
  have hdiff : ∀ t ∈ uIcc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t : ℝ => Complex.exp (t * w)) t :=
    fun t _ => (hF t).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => w * Complex.exp (t * w)) (uIcc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    apply Complex.continuous_exp.comp
    exact continuous_ofReal.mul_const w
  have hftc := integral_deriv_eq_sub' (fun t : ℝ => Complex.exp (t * w))
    hderivfun hdiff hcont
  rw [intervalIntegral.integral_const_mul] at hftc
  simpa using hftc.symm

/-- Averaging operator: `E1 u = ∫_0^1 exp (t * u)`. -/
noncomputable def E1 (u : ℂ) : ℂ := ∫ t : ℝ in (0:ℝ)..1, Complex.exp (t * u)

/-- `E1 0 = 1`. -/
theorem E1_zero : E1 0 = 1 := by
  simp only [E1]
  simp

/-- `E1` agrees with the difference quotient off `0`. -/
theorem E1_eq_div (u : ℂ) (hu : u ≠ 0) : E1 u = (Complex.exp u - 1) / u := by
  have h := exp_sub_one_eq u
  simp only [E1]
  rw [eq_div_iff hu, mul_comm]
  exact h.symm

/-- `‖E1 v - 1‖ ≤ ‖v‖` for `‖v‖ ≤ 1`. -/
theorem E1_sub_one_le (v : ℂ) (hv : ‖v‖ ≤ 1) : ‖E1 v - 1‖ ≤ ‖v‖ := by
  by_cases h0 : v = 0
  · simp [h0, E1_zero]
  · have h1 : E1 v - 1 = (Complex.exp v - 1 - v) / v := by
      rw [E1_eq_div v h0, eq_div_iff h0, sub_mul, div_mul_cancel₀ _ h0, one_mul]
    rw [h1, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr h0)]
    calc ‖Complex.exp v - 1 - v‖ ≤ ‖v‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hv
      _ = ‖v‖ * ‖v‖ := by ring

/-- `E1` is continuous at `0`. -/
theorem E1_continuousAt_zero : ContinuousAt E1 0 := by
  rw [ContinuousAt, E1_zero]
  have hbound : ∀ᶠ v : ℂ in 𝓝 0, ‖E1 v - 1‖ ≤ ‖v‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with v hv
    apply E1_sub_one_le
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact le_of_lt hv
  have hnorm : Tendsto (fun v : ℂ => ‖v‖) (𝓝 0) (𝓝 0) := by
    have h := continuous_norm.continuousAt (x := (0 : ℂ))
    rw [ContinuousAt] at h
    simpa using h
  have h := squeeze_zero_norm' hbound hnorm
  simpa using h.add_const (1 : ℂ)

/-- `E1` is continuous everywhere. -/
theorem E1_continuous : Continuous E1 := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · rw [hu]
    exact E1_continuousAt_zero
  · have heq : E1 =ᶠ[𝓝 u] fun v => (Complex.exp v - 1) / v := by
      filter_upwards [eventually_ne_nhds hu] with v hv using E1_eq_div v hv
    exact ContinuousAt.congr
      ((Complex.continuous_exp.sub continuous_const).continuousAt.div continuousAt_id hu)
      heq.symm

/-- Derivative of `E1` under the integral sign. -/
theorem E1_hasDerivAt (x₀ : ℂ) :
    HasDerivAt E1 (∫ t in (0:ℝ)..1, (t : ℂ) * Complex.exp ((t : ℂ) * x₀)) x₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume)
    (F := fun x t => Complex.exp ((t : ℂ) * x))
    (F' := fun x t => (t : ℂ) * Complex.exp ((t : ℂ) * x))
    (x₀ := x₀) (s := Metric.ball x₀ 1) (a := (0:ℝ)) (b := (1:ℝ))
    (bound := fun _ => Real.exp (‖x₀‖ + 1))
    (Metric.ball_mem_nhds x₀ (by norm_num))
    (Filter.Eventually.of_forall fun x =>
      (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).aestronglyMeasurable)
    ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).intervalIntegrable 0 1)
    ((Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht01 : 0 ≤ t ∧ t ≤ 1 := by
        rw [Set.mem_uIoc] at ht
        rcases ht with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> constructor <;> linarith
      have hx0 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have hdist : dist x x₀ < 1 := Metric.mem_ball.mp hx
        have hle : ‖x‖ ≤ ‖x₀‖ + dist x x₀ := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by congr 1; abel
            _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        linarith
      have htn : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
        have h : ‖((t : ℝ) : ℂ)‖ = |t| := RCLike.norm_ofReal t
        rw [h, abs_of_nonneg ht01.1]
        exact ht01.2
      have hxt : ‖(t : ℂ) * x‖ ≤ ‖x‖ := by
        rw [norm_mul]
        calc ‖(t : ℂ)‖ * ‖x‖ ≤ 1 * ‖x‖ :=
              mul_le_mul_of_nonneg_right htn (norm_nonneg _)
          _ = ‖x‖ := one_mul _
      calc ‖(t : ℂ) * Complex.exp ((t : ℂ) * x)‖
          = ‖(t : ℂ)‖ * ‖Complex.exp ((t : ℂ) * x)‖ := norm_mul _ _
        _ ≤ 1 * Real.exp (‖x₀‖ + 1) := by
            apply mul_le_mul htn _ (norm_nonneg _) zero_le_one
            calc ‖Complex.exp ((t : ℂ) * x)‖ ≤ Real.exp ‖(t : ℂ) * x‖ :=
                  Complex.norm_exp_le_exp_norm _
              _ ≤ Real.exp (‖x₀‖ + 1) := by
                  apply Real.exp_le_exp.mpr
                  calc ‖(t : ℂ) * x‖ ≤ ‖x‖ := hxt
                    _ ≤ ‖x₀‖ + 1 := hx0
        _ = Real.exp (‖x₀‖ + 1) := one_mul _)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => by
      have h1 : HasDerivAt (fun x : ℂ => (t : ℂ) * x) (t : ℂ) x := by
        simpa using (hasDerivAt_id x).const_mul (t : ℂ)
      have h2 := h1.cexp
      rwa [mul_comm (t : ℂ) (Complex.exp ((t : ℂ) * x))] )
  have hE1 : E1 = fun x => ∫ t in (0:ℝ)..1, Complex.exp ((t : ℂ) * x) := rfl
  rw [hE1]
  exact key.2

/-- `E1` is differentiable everywhere. -/
theorem E1_differentiable : Differentiable ℂ E1 :=
  fun x₀ => (E1_hasDerivAt x₀).differentiableAt

/-- Entire extension of `(y^s - 1)/s` via the averaging operator. -/
noncomputable def perronRemainder (y : ℝ) (s : ℂ) : ℂ :=
  Real.log y * E1 (s * Real.log y)

/-- The remainder is entire in `s`: constant times `E1` of a linear map. -/
theorem perronRemainder_differentiable (y : ℝ) :
    Differentiable ℂ (perronRemainder y) := by
  have hEq : perronRemainder y
      = fun s => (Real.log y : ℂ) * E1 (s * (Real.log y : ℂ)) := rfl
  rw [hEq]
  intro s
  have hlin : DifferentiableAt ℂ (fun s : ℂ => s * (Real.log y : ℂ)) s :=
    differentiableAt_id.mul_const _
  exact (differentiableAt_const _).mul ((E1_differentiable _).comp s hlin)

/-- Agreement with the quotient off `0`. -/
theorem perronRemainder_eq_div {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    perronRemainder y s = ((y : ℂ) ^ s - 1) / s := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  have hcpow : (y : ℂ) ^ s = Complex.exp (s * Real.log y) := by
    rw [Complex.cpow_def_of_ne_zero hy' s, Complex.ofReal_log hy.le]
    congr 1
    ring
  by_cases hL : Real.log y = 0
  · have hy1 : y = 1 := by
      have h := Real.exp_log hy
      rw [hL, Real.exp_zero] at h
      exact h.symm
    simp only [perronRemainder, hL, Complex.ofReal_zero, zero_mul]
    rw [hy1]
    simp [Complex.one_cpow]
  · have hLc : (Real.log y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
    have hsL : s * Real.log y ≠ 0 := mul_ne_zero hs hLc
    simp only [perronRemainder, E1_eq_div _ hsL]
    rw [hcpow]
    field_simp

/-- Slope of the remainder at `0`, in integral form. -/
theorem perronRemainder_slope {y : ℝ} {h : ℂ} (hh : h ≠ 0) :
    (perronRemainder y h - perronRemainder y 0) / h
      = (Real.log y : ℂ) ^ 2 * ∫ t : ℝ in (0:ℝ)..1, t * E1 (t * h * Real.log y) := by
  have hg0 : perronRemainder y 0 = Real.log y := by
    simp [perronRemainder, E1_zero]
  have hexp1 : ∀ t : ℝ, Complex.exp (t * h * Real.log y) - 1
      = (t * h * Real.log y) * E1 (t * h * Real.log y) := by
    intro t
    by_cases hv : (t : ℂ) * h * Real.log y = 0
    · simp [hv]
    · rw [E1_eq_div _ hv, mul_div_cancel₀ _ hv]
  have h1 : (1 : ℂ) = ∫ t : ℝ in (0:ℝ)..1, 1 := by simp
  have hcont : Continuous (fun t : ℝ => Complex.exp (t * h * Real.log y)) :=
    Complex.continuous_exp.comp ((continuous_ofReal.mul_const h).mul_const _)
  have hdiff : perronRemainder y h - perronRemainder y 0
      = (Real.log y : ℂ) * ∫ t : ℝ in (0:ℝ)..1,
        (Complex.exp (t * h * Real.log y) - 1) := by
    have e0 : perronRemainder y 0 = (Real.log y : ℂ) * ∫ t : ℝ in (0:ℝ)..1, 1 := by
      rw [hg0, ← h1]
      ring
    rw [e0]
    simp only [perronRemainder, E1, ← mul_assoc]
    rw [← mul_sub, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
  rw [hdiff]
  simp_rw [hexp1]
  have hfac : ∀ t : ℝ, ((t : ℂ) * h * Real.log y) * E1 (t * h * Real.log y)
      = (h * Real.log y) * ((t : ℂ) * E1 (t * h * Real.log y)) := fun t => by ring
  simp_rw [hfac, intervalIntegral.integral_const_mul]
  field_simp


/-- Norm of a positive real base to a complex power. -/
theorem norm_cpow_ofReal {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖(y : ℂ) ^ s‖ = Real.exp (s.re * Real.log y) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  rw [Complex.cpow_def_of_ne_zero hy' s, ← Complex.ofReal_log hy.le, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- The kernel quotient as remainder plus pole part. -/
theorem cpow_div_eq_remainder_add {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    (y : ℂ) ^ s / s = perronRemainder y s + 1 / s := by
  rw [perronRemainder_eq_div hy hs, ← add_div, sub_add_cancel]

/-- Integral of `exp (L * x)` over `[a, b]`. -/
theorem integral_exp_mul {L a b : ℝ} (hL : L ≠ 0) :
    ∫ x : ℝ in a..b, Real.exp (L * x)
      = (Real.exp (L * b) - Real.exp (L * a)) / L := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (L * x) / L)
      (Real.exp (L * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => L * x) L x := by
      simpa using (hasDerivAt_id (x : ℝ)).const_mul L
    have h3 := h1.exp.div_const L
    have hval : Real.exp (L * x) * L / L = Real.exp (L * x) :=
      mul_div_cancel_right₀ _ hL
    rwa [hval] at h3
  have hderivfun : deriv (fun x => Real.exp (L * x) / L)
      = fun x => Real.exp (L * x) :=
    funext fun x => (hderiv x).deriv
  have hdiff : ∀ x ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun x => Real.exp (L * x) / L) x :=
    fun x _ => (hderiv x).differentiableAt
  have hcont : ContinuousOn (fun x => Real.exp (L * x)) (Set.uIcc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have h := integral_deriv_eq_sub' (fun x => Real.exp (L * x) / L)
    hderivfun hdiff hcont
  rw [h]
  exact (sub_div _ _ _).symm

/-- Horizontal side bound for `y > 1`, uniform in the left endpoint. -/
theorem horiz_side_bound_gt_one {y U c T e : ℝ} (hy : 0 < y) (hy1 : 1 < y)
    (hU : 0 < U) (hc : 0 < c) (hT : 0 < T) (he : e = T ∨ e = -T) :
    ‖∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * c) / Real.log y / T := by
  have hL : 0 < Real.log y := Real.log_pos hy1
  have hab : -U ≤ c := le_of_lt ((neg_lt_zero.mpr hU).trans hc)
  have hpt : ∀ x : ℝ, ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * x) / T := by
    intro x
    have hre : ((x : ℂ) + (e : ℂ) * Complex.I).re = x := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have him : |(((x : ℂ) + (e : ℂ) * Complex.I).im)| = T := by
      have him' : ((x : ℂ) + (e : ℂ) * Complex.I).im = e := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [him']
      rcases he with rfl | rfl
      · exact abs_of_pos hT
      · rw [abs_neg]; exact abs_of_pos hT
    have hTs : T ≤ ‖(x : ℂ) + (e : ℂ) * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [him] at h
    have hnorm : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) := by
      have h := norm_cpow_ofReal hy ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [hre, mul_comm x _] at h
    have e1 : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
        / ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) * (1 / ‖(x : ℂ) + (e : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * x) / T
        = Real.exp (Real.log y * x) * (1 / T) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le hT hTs
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun x => Real.exp (Real.log y * x) / T)
    hab (Filter.Eventually.of_forall fun x _ => hpt x)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const T
      |>.intervalIntegrable _ _)
  have hval : ∫ x : ℝ in (-U)..c, Real.exp (Real.log y * x) / T
      = (Real.exp (Real.log y * c) - Real.exp (Real.log y * (-U)))
        / Real.log y / T := by
    have hfun : (fun x => Real.exp (Real.log y * x) / T)
        = fun x => (1 / T) * Real.exp (Real.log y * x) := by
      funext x; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_exp_mul (ne_of_gt hL)]
    ring
  rw [hval] at hInt
  apply hInt.trans
  apply div_le_div_of_nonneg_right _ hT.le
  apply div_le_div_of_nonneg_right _ hL.le
  exact sub_le_self _ (Real.exp_nonneg _)

/-- Vertical side bound at real part `d ≠ 0`. -/
theorem vert_side_bound {y d T : ℝ} (hy : 0 < y) (hd : d ≠ 0) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
      / ((d : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * d) / |d|) := by
  have hab : -T ≤ T := le_of_lt (neg_lt_self hT)
  have hpt : ∀ t : ℝ, ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
      / ((d : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * d) / |d| := by
    intro t
    have hre : ((d : ℂ) + (t : ℂ) * Complex.I).re = d := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have hds : |d| ≤ ‖(d : ℂ) + (t : ℂ) * Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((d : ℂ) + (t : ℂ) * Complex.I)
      rwa [hre] at h
    have hnorm : ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * d) := by
      have h := norm_cpow_ofReal hy ((d : ℂ) + (t : ℂ) * Complex.I)
      rwa [hre, mul_comm d _] at h
    have e1 : ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
        / ((d : ℂ) + (t : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * d) * (1 / ‖(d : ℂ) + (t : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * d) / |d|
        = Real.exp (Real.log y * d) * (1 / |d|) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le (abs_pos.mpr hd) hds
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun _ => Real.exp (Real.log y * d) / |d|)
    hab (Filter.Eventually.of_forall fun t _ => hpt t)
    (continuous_const.intervalIntegrable _ _)
  have hval : ∫ t : ℝ in (-T)..T, Real.exp (Real.log y * d) / |d|
      = 2 * T * (Real.exp (Real.log y * d) / |d|) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hval] at hInt
  exact hInt

/-- Left-side corollary: `d = -U`. -/
theorem vert_side_bound_left {y U T : ℝ} (hy : 0 < y) (hU : 0 < U) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * (-U)) / U) := by
  have h := vert_side_bound (d := -U) hy (ne_of_lt (neg_lt_zero.mpr hU)) hT
  rwa [abs_neg, abs_of_pos hU] at h

/-- Right-side corollary: `d = U`. -/
theorem vert_side_bound_right {y U T : ℝ} (hy : 0 < y) (hU : 0 < U) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * U) / U) := by
  have h := vert_side_bound (d := U) hy (ne_of_gt hU) hT
  rwa [abs_of_pos hU] at h

/-- Rectangle identity for `y^s/s` with the pole inside (`y > 1` case). -/
theorem rect_identity_gt_one {y U c T : ℝ} (hy : 0 < y) (hU : 0 < U) (hc : 0 < c)
    (hT : 0 < T) :
    (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      + Complex.I * ((∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = 2 * Real.pi * Complex.I := by
  have hbot : ∀ x : ℝ, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have htop : ∀ x : ℝ, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have hright : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hc]
  have hleft : ∀ t : ℝ, (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hU]
  have hRcont : Continuous (perronRemainder y) :=
    (perronRemainder_differentiable y).continuous
  have hsplit_b : (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-U)..c, perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in (-U)..c, (1 : ℂ) / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (hbot x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => hbot x)).intervalIntegrable _ _
  have hsplit_t : (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-U)..c, perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in (-U)..c, (1 : ℂ) / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (htop x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => htop x)).intervalIntegrable _ _
  have hsplit_r : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I)
          + 1 / ((c : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hright t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hright t)).intervalIntegrable _ _
  have hsplit_l : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          + 1 / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hleft t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hleft t)).intervalIntegrable _ _
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRemainder y) (Complex.mk (-U) (-T)) (Complex.mk c T)
    ((perronRemainder_differentiable y).differentiableOn)
  have hR' : (∫ x : ℝ in (-U)..c,
          perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-U)..c,
          perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = 0 := hR
  have h1 := boundary_rect_one_div (a := -U) (b := c)
    (neg_lt_zero.mpr hU) hc hT
  rw [← Complex.ofReal_neg] at h1
  rw [hsplit_b, hsplit_t, hsplit_r, hsplit_l]
  simp only [smul_eq_mul] at hR'
  linear_combination hR' + h1

/-- Horizontal side bound over `[c, U]`, exact value (no sign hypothesis on `L`). -/
theorem horiz_side_bound_exact {y U c T e : ℝ} (hy : 0 < y)
    (hcU : c ≤ U) (hT : 0 < T) (he : e = T ∨ e = -T) (hL : Real.log y ≠ 0) :
    ‖∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T := by
  have hpt : ∀ x : ℝ, ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * x) / T := by
    intro x
    have hre : ((x : ℂ) + (e : ℂ) * Complex.I).re = x := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have him : |(((x : ℂ) + (e : ℂ) * Complex.I).im)| = T := by
      have him' : ((x : ℂ) + (e : ℂ) * Complex.I).im = e := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [him']
      rcases he with rfl | rfl
      · exact abs_of_pos hT
      · rw [abs_neg]; exact abs_of_pos hT
    have hTs : T ≤ ‖(x : ℂ) + (e : ℂ) * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [him] at h
    have hnorm : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) := by
      have h := norm_cpow_ofReal hy ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [hre, mul_comm x _] at h
    have e1 : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
        / ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) * (1 / ‖(x : ℂ) + (e : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * x) / T
        = Real.exp (Real.log y * x) * (1 / T) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le hT hTs
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun x => Real.exp (Real.log y * x) / T)
    hcU (Filter.Eventually.of_forall fun x _ => hpt x)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const T
      |>.intervalIntegrable _ _)
  have hval : ∫ x : ℝ in c..U, Real.exp (Real.log y * x) / T
      = (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T := by
    have hfun : (fun x => Real.exp (Real.log y * x) / T)
        = fun x => (1 / T) * Real.exp (Real.log y * x) := by
      funext x; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul hL]
    ring
  rw [hval] at hInt
  exact hInt

/-- Rectangle identity for `y^s/s` with the pole outside (`y < 1` case). -/
theorem rect_identity_lt_one {y U c T : ℝ} (hy : 0 < y) (hcU : c < U) (hc : 0 < c)
    (hT : 0 < T) :
    (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      + Complex.I * ((∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)))
      = 0 := by
  have hU : 0 < U := lt_trans hc hcU
  have hbot : ∀ x : ℝ, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have htop : ∀ x : ℝ, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have hright : ∀ t : ℝ, (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hU]
  have hleft : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hc]
  have hRcont : Continuous (perronRemainder y) :=
    (perronRemainder_differentiable y).continuous
  have hsplit_b : (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in c..U, perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in c..U, (1 : ℂ) / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (hbot x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => hbot x)).intervalIntegrable _ _
  have hsplit_t : (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in c..U, perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in c..U, (1 : ℂ) / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (htop x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => htop x)).intervalIntegrable _ _
  have hsplit_r : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          + 1 / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hright t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hright t)).intervalIntegrable _ _
  have hsplit_l : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I)
          + 1 / ((c : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hleft t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hleft t)).intervalIntegrable _ _
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRemainder y) (Complex.mk c (-T)) (Complex.mk U T)
    ((perronRemainder_differentiable y).differentiableOn)
  have hR' : (∫ x : ℝ in c..U,
          perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in c..U,
          perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        = 0 := hR
  have h1 := boundary_rect_one_div_outside (a := c) (b := U) hc hcU.le hT
  rw [← Complex.ofReal_neg] at h1
  rw [hsplit_b, hsplit_t, hsplit_r, hsplit_l]
  simp only [smul_eq_mul] at hR'
  linear_combination hR' + h1

/-- Truncated Perron bound for `y > 1`. -/
theorem perron_bound_gt_one {y c T : ℝ} (hy : 0 < y) (hy1 : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - 1‖ ≤ Real.exp (Real.log y * c) / Real.log y / T / Real.pi := by
  have hL : 0 < Real.log y := Real.log_pos hy1
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖(2:ℂ)‖ = 2 := by
    have hcast : (2:ℂ) = ((2:ℝ):ℂ) := by exact_mod_cast rfl
    rw [hcast]
    calc ‖((2:ℝ):ℂ)‖ = |(2:ℝ)| := RCLike.norm_ofReal 2
      _ = 2 := by norm_num
  have hpiN : ‖((Real.pi:ℝ):ℂ)‖ = Real.pi := by
    calc ‖((Real.pi:ℝ):ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      _ = Real.pi := abs_of_pos Real.pi_pos
  have h2piN : ‖((2:ℂ) * Real.pi)‖ = 2 * Real.pi := by
    rw [norm_mul, h2, hpiN]
  have h2piI : ‖((2:ℂ) * Real.pi) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, h2piN, Complex.norm_I, mul_one]
  have hR : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = 2 * Real.pi * perronKernel y c T := by
    have hKdef : perronKernel y c T = (1 / (2 * Real.pi))
        * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)) := rfl
    have hpi : ((2:ℂ) * Real.pi) ≠ 0 := mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hKdef, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have heqU : ∀ U : ℝ,
      (Real.exp (Real.log y * c) / Real.log y / T
        + Real.exp (Real.log y * c) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * (-U)) / U)) / (2 * Real.pi)
      = Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
    intro U; ring
  have hperU : ∀ U : ℝ, 1 ≤ U → ‖perronKernel y c T - 1‖
      ≤ Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
    intro U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hrect := rect_identity_gt_one hy hU hc hT
    have hRsmul : Complex.I
          * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        = Complex.I * (2 * Real.pi * perronKernel y c T) := by rw [hR]
    have hKey : ((2:ℂ) * Real.pi * Complex.I) * (perronKernel y c T - 1)
        = ((∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
          + Complex.I * (∫ t : ℝ in (-T)..T,
            (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      linear_combination hrect - hRsmul
    have hnorm : 2 * Real.pi * ‖perronKernel y c T - 1‖
        ≤ ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) hKey
      rw [norm_mul, h2piI] at h
      rw [h]
      have a : ‖((∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
            - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))‖
          ≤ ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
            + ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖ :=
        norm_sub_le _ _
      have b : ‖Complex.I * (∫ t : ℝ in (-T)..T,
              (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
    have hTle : ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.exp (Real.log y * c) / Real.log y / T :=
      horiz_side_bound_gt_one hy hy1 hU hc hT (Or.inl rfl)
    have hBle : ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.exp (Real.log y * c) / Real.log y / T :=
      horiz_side_bound_gt_one hy hy1 hU hc hT (Or.inr rfl)
    have hVle : ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 2 * T * (Real.exp (Real.log y * (-U)) / U) :=
      vert_side_bound_left hy hU hT
    have hdiv : ‖perronKernel y c T - 1‖
        ≤ (Real.exp (Real.log y * c) / Real.log y / T
          + Real.exp (Real.log y * c) / Real.log y / T
          + 2 * T * (Real.exp (Real.log y * (-U)) / U)) / (2 * Real.pi) := by
      rw [le_div_iff₀ h2pi, mul_comm]
      refine hnorm.trans ?_
      exact add_le_add (add_le_add hTle hBle) hVle
    rw [heqU U] at hdiv
    exact hdiv
  have hUL : Filter.Tendsto (fun U : ℝ => U * Real.log y) Filter.atTop
      Filter.atTop := by
    have h := Filter.Tendsto.const_mul_atTop hL (tendsto_id (x := Filter.atTop))
    have hform2 : (fun U : ℝ => U * Real.log y)
        = fun U => Real.log y * id U := by
      funext U; simp [mul_comm]
    rw [hform2]; exact h
  have hexp2 : Filter.Tendsto (fun U : ℝ => Real.exp (Real.log y * (-U)))
      Filter.atTop (𝓝 0) := by
    have hexp : Filter.Tendsto (fun U : ℝ => Real.exp (-(U * Real.log y)))
        Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hUL
    have hcongr : (fun U : ℝ => Real.exp (Real.log y * (-U)))
        = fun U => Real.exp (-(U * Real.log y)) := by
      funext U; congr 1; ring
    rw [hcongr]; exact hexp
  have hB2 : Filter.Tendsto (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / Real.pi)
      Filter.atTop (𝓝 0) := by
    have hform : (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / Real.pi)
        = fun U => (T / Real.pi) * Real.exp (Real.log y * (-U)) := by
      funext U; ring
    rw [hform]
    have hmul := Filter.Tendsto.const_mul (T / Real.pi) hexp2
    simpa using hmul
  have he0 : Filter.Tendsto
      (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / (U * Real.pi))
      Filter.atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB2
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hnn : 0 ≤ T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hform3 : T * Real.exp (Real.log y * (-U)) / (U * Real.pi)
        = (T * Real.exp (Real.log y * (-U)) / Real.pi) / U := by ring
    rw [hform3]
    apply div_le_self _ hU1
    positivity
  have hCg : Filter.Tendsto
      (fun U : ℝ => Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi))
      Filter.atTop
      (𝓝 (Real.exp (Real.log y * c) / Real.log y / T / Real.pi)) := by
    have h := (tendsto_const_nhds (x := Real.exp (Real.log y * c) / Real.log y / T
      / Real.pi)).add he0
    simpa using h
  have hCf : Filter.Tendsto (fun _ : ℝ => ‖perronKernel y c T - 1‖) Filter.atTop
      (𝓝 ‖perronKernel y c T - 1‖) := tendsto_const_nhds
  have hle : (fun _ : ℝ => ‖perronKernel y c T - 1‖) ≤ᶠ[Filter.atTop]
      (fun U : ℝ => Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    exact hperU U hU1
  exact le_of_tendsto_of_tendsto hCf hCg hle

/-- Truncated Perron bound for `y < 1`. -/
theorem perron_bound_lt_one {y c T : ℝ} (hy : 0 < y) (hylt : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
  have hL : Real.log y < 0 := Real.log_neg hy hylt
  have hLne : Real.log y ≠ 0 := ne_of_lt hL
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖(2:ℂ)‖ = 2 := by
    have hcast : (2:ℂ) = ((2:ℝ):ℂ) := by exact_mod_cast rfl
    rw [hcast]
    calc ‖((2:ℝ):ℂ)‖ = |(2:ℝ)| := RCLike.norm_ofReal 2
      _ = 2 := by norm_num
  have hpiN : ‖((Real.pi:ℝ):ℂ)‖ = Real.pi := by
    calc ‖((Real.pi:ℝ):ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      _ = Real.pi := abs_of_pos Real.pi_pos
  have h2piN : ‖((2:ℂ) * Real.pi)‖ = 2 * Real.pi := by
    rw [norm_mul, h2, hpiN]
  have h2piI : ‖((2:ℂ) * Real.pi) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, h2piN, Complex.norm_I, mul_one]
  have hR : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = 2 * Real.pi * perronKernel y c T := by
    have hKdef : perronKernel y c T = (1 / (2 * Real.pi))
        * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)) := rfl
    have hpi : ((2:ℂ) * Real.pi) ≠ 0 := mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hKdef, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have hperU : ∀ U : ℝ, max c 1 < U → ‖perronKernel y c T‖
      ≤ ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi) := by
    intro U hmaxU
    have hcU : c < U := lt_of_le_of_lt (le_max_left _ _) hmaxU
    have hU : 0 < U := lt_trans hc hcU
    have hrect := rect_identity_lt_one hy hcU hc hT
    have hRsmul : Complex.I
          * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        = Complex.I * (2 * Real.pi * perronKernel y c T) := by rw [hR]
    have hKey : ((2:ℂ) * Real.pi * Complex.I) * perronKernel y c T
        = ((∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))
          + Complex.I * (∫ t : ℝ in (-T)..T,
            (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      linear_combination -hrect - hRsmul
    have hnorm : 2 * Real.pi * ‖perronKernel y c T‖
        ≤ ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) hKey
      rw [norm_mul, h2piI] at h
      rw [h]
      have a : ‖((∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
            - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))‖
          ≤ ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
            + ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖ :=
        norm_sub_le _ _
      have b : ‖Complex.I * (∫ t : ℝ in (-T)..T,
              (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
    have hBle : ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
        ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
          / Real.log y / T :=
      horiz_side_bound_exact hy hcU.le hT (Or.inr rfl) hLne
    have hTle : ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
        ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
          / Real.log y / T :=
      horiz_side_bound_exact hy hcU.le hT (Or.inl rfl) hLne
    have hVle : ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 2 * T * (Real.exp (Real.log y * U) / U) :=
      vert_side_bound_right hy hU hT
    have hdiv : ‖perronKernel y c T‖
        ≤ ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
          + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
          + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi) := by
      rw [le_div_iff₀ h2pi, mul_comm]
      refine hnorm.trans ?_
      exact add_le_add (add_le_add hBle hTle) hVle
    exact hdiv
  have hUL' : Filter.Tendsto (fun U : ℝ => (-Real.log y) * U) Filter.atTop
      Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (neg_pos.mpr hL) (tendsto_id (x := Filter.atTop))
  have hexpU : Filter.Tendsto (fun U : ℝ => Real.exp (Real.log y * U))
      Filter.atTop (𝓝 0) := by
    have hexp : Filter.Tendsto
        (fun U : ℝ => Real.exp (-((-Real.log y) * U))) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hUL'
    have hcongr : (fun U : ℝ => Real.exp (Real.log y * U))
        = fun U => Real.exp (-((-Real.log y) * U)) := by
      funext U; congr 1; ring
    rw [hcongr]; exact hexp
  have hB : Filter.Tendsto
      (fun U : ℝ => (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T) Filter.atTop
      (𝓝 ((0 - Real.exp (Real.log y * c)) / Real.log y / T)) :=
    ((hexpU.sub_const _).div_const _).div_const _
  have hbU : Filter.Tendsto (fun U : ℝ => 2 * T * Real.exp (Real.log y * U))
      Filter.atTop (𝓝 0) := by
    have hmul := Filter.Tendsto.const_mul (2 * T) hexpU
    simpa using hmul
  have hV : Filter.Tendsto (fun U : ℝ => 2 * T * (Real.exp (Real.log y * U) / U))
      Filter.atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbU
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hnn : 0 ≤ 2 * T * (Real.exp (Real.log y * U) / U) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hle : Real.exp (Real.log y * U) / U ≤ Real.exp (Real.log y * U) :=
      div_le_self (Real.exp_nonneg _) hU1
    apply mul_le_mul_of_nonneg_left hle
    positivity
  have hg : Filter.Tendsto
      (fun U : ℝ => ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi)) Filter.atTop
      (𝓝 (((0 - Real.exp (Real.log y * c)) / Real.log y / T
        + (0 - Real.exp (Real.log y * c)) / Real.log y / T + 0) / (2 * Real.pi))) :=
    (((hB.add hB).add hV).div_const _)
  have hC0 : (((0 - Real.exp (Real.log y * c)) / Real.log y / T
        + (0 - Real.exp (Real.log y * c)) / Real.log y / T + 0) / (2 * Real.pi))
      = Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
    rw [abs_of_neg hL]
    ring
  rw [hC0] at hg
  have hCf : Filter.Tendsto (fun _ : ℝ => ‖perronKernel y c T‖) Filter.atTop
      (𝓝 ‖perronKernel y c T‖) := tendsto_const_nhds
  have hle : (fun _ : ℝ => ‖perronKernel y c T‖) ≤ᶠ[Filter.atTop]
      (fun U : ℝ => ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi)) := by
    filter_upwards [Filter.eventually_ge_atTop (max c 1 + 1)] with U hU
    have hmax : max c 1 < U := lt_of_lt_of_le (lt_add_one _) hU
    exact hperU U hmax
  exact le_of_tendsto_of_tendsto hCf hg hle

/-- Truncated Perron formula with explicit Schoenfeld-shape error bound. -/
theorem perron_bound {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - (if 1 < y then (1:ℂ) else 0)‖
      ≤ Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
  rcases lt_or_gt_of_ne hy1 with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), sub_zero]
    exact perron_bound_lt_one hy h hc hT
  · rw [ite_eq_left h, abs_of_pos (Real.log_pos h)]
    exact perron_bound_gt_one hy h hc hT

end PerronKernel
