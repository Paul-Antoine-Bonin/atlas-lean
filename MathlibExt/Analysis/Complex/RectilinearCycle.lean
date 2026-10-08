/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite rectilinear cycles

The explicit rectangle-residue calculation below was adapted from
`MathlibExt.Analysis.PerronKernel`; that module records its Apache-2.0 upstream
source and detailed provenance.

This file develops the finite integer combinations of oriented rectangle
boundaries needed for contour integration.  For the contour-existence and
Riesz-integral arguments, a rectilinear cycle is represented by a finite
integer combination of
oriented rectangle boundaries.  These boundaries are rectifiable, and
integer coefficients make reversal and cancellation of shared boundary
pieces algebraic.  A smooth-contour refinement is not claimed by this
abstraction.

The integral below is the Banach-valued boundary integral appearing in
Mathlib's rectangular Cauchy--Goursat theorem.  In particular, it is an
actual Bochner contour integral, not an unconstrained functional bundled with
the conclusion that it should satisfy.

This module supplies the finite-cycle and Cauchy--Goursat leaves.  The
geometric existence of a cycle separating a compact set from the complement
of an open neighborhood, and the resulting Riesz-integral independence, are
kept in later modules.
-/

@[expose] public section


open scoped Interval
open Set
namespace Complex

open Filter MeasureTheory Set intervalIntegral

open Real in
/-- Scaled arctan integral, via FTC on `arctan (x / d)`. -/
theorem integral_div_add_sq {d a b : ℝ} (hc : d ≠ 0) :
    ∫ x : ℝ in a..b, d / (x ^ 2 + d ^ 2) = arctan (b / d) - arctan (a / d) := by
  have hsq : (0 : ℝ) < d ^ 2 := sq_pos_iff.mpr hc
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => arctan (x / d)) (d / (x ^ 2 + d ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x / d) (1 / d) x := by
      have h := (hasDerivAt_id (x : ℝ)).mul_const (d⁻¹ : ℝ)
      simpa [div_eq_mul_inv, one_mul] using h
    have h2 := h1.arctan
    have hval : 1 / (1 + (x / d) ^ 2) * (1 / d) = d / (x ^ 2 + d ^ 2) := by
      field_simp
      ring
    rw [hval] at h2
    exact h2
  have hderivfun : deriv (fun x => arctan (x / d)) = fun x => d / (x ^ 2 + d ^ 2) :=
    funext fun x => (hderiv x).deriv
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (fun x => arctan (x / d)) x :=
    fun x _ => (hderiv x).differentiableAt
  have hcont : ContinuousOn (fun x => d / (x ^ 2 + d ^ 2)) (uIcc a b) := by
    apply Continuous.continuousOn
    apply Continuous.div continuous_const (continuous_id.pow 2 |>.add continuous_const)
    intro x
    exact ne_of_gt (lt_of_lt_of_le hsq (le_add_of_nonneg_left (sq_nonneg x)))
  exact integral_deriv_eq_sub' _ hderivfun hdiff hcont

/-- Integral of an odd real function over a symmetric interval vanishes. -/
theorem odd_integral_eq_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (T : ℝ) :
    ∫ x : ℝ in (-T)..T, f x = 0 := by
  have hcomp : ∫ x : ℝ in (-T)..T, f (-x) = ∫ x : ℝ in (-T)..T, f x := by
    have h := integral_comp_neg (a := -T) (b := T) (f := f)
    simp only [neg_neg] at h
    exact h
  have hodd' : ∫ x : ℝ in (-T)..T, f (-x) = -∫ x : ℝ in (-T)..T, f x := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith [hcomp, hodd']

open Real in
/-- Vertical side integral of `1/s`: `2 * arctan (T / c)`. -/
theorem vertical_side_one_div {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) :
    ∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I) = 2 * arctan (T / c) := by
  have hab : -T ≤ T := by linarith
  have hcont : Continuous (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) := by
    apply Continuous.div continuous_const
      (continuous_const.add (continuous_ofReal.mul continuous_const))
    intro y h
    apply hc
    have := congrArg Complex.re h
    simpa using this
  have hf : IntegrableOn (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) (Ioc (-T) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcont.intervalIntegrable _ _)
  have hfi : IntervalIntegrable (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) volume (-T) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hf
  have hre_integral :
      (∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I)).re =
        ∫ y : ℝ in (-T)..T, ((1 : ℂ) / (c + y * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hfi).symm
  have him_integral :
      (∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I)).im =
        ∫ y : ℝ in (-T)..T, ((1 : ℂ) / (c + y * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hfi).symm
  have hre : ∀ y : ℝ, ((1 : ℂ) / (c + y * Complex.I)).re = c / (y ^ 2 + c ^ 2) := by
    intro y
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_add_mul_I]
    field_simp
    ring
  have him : ∀ y : ℝ, ((1 : ℂ) / (c + y * Complex.I)).im = -y / (y ^ 2 + c ^ 2) := by
    intro y
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.normSq_add_mul_I]
    field_simp
    ring
  apply Complex.ext
  · rw [hre_integral]
    simp only [hre, integral_div_add_sq hc]
    rw [show (-T) / c = -(T / c) by ring, arctan_neg]
    have h2re : (2 : ℂ).re = 2 := rfl
    have h2im : (2 : ℂ).im = 0 := rfl
    rw [Complex.mul_re, h2re, h2im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [him_integral]
    simp_rw [him]
    have hodd : ∀ y : ℝ, -(-y) / ((-y) ^ 2 + c ^ 2) = -(-y / (y ^ 2 + c ^ 2)) := by
      intro y
      rw [show (-y) ^ 2 = y ^ 2 by ring]
      ring
    have h0 := odd_integral_eq_zero (f := fun y => -y / (y ^ 2 + c ^ 2)) hodd T
    simp only [h0]
    simp

open Real in
/-- Bottom-minus-top of `1/s`: `2i·Δarctan` (log parts cancel). -/
theorem horiz_diff_one_div {a b T : ℝ} (hT : T ≠ 0) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      = 2 * Complex.I * (arctan (b / T) - arctan (a / T)) := by
  have hcb : ∀ x : ℝ, ((x : ℂ) + -T * Complex.I) ≠ 0 := by
    intro x h
    apply hT
    have := congrArg Complex.im h
    simpa using this
  have hct : ∀ x : ℝ, ((x : ℂ) + T * Complex.I) ≠ 0 := by
    intro x h
    apply hT
    have := congrArg Complex.im h
    simpa using this
  have hcontb : Continuous (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I)) :=
    Continuous.div continuous_const
      (continuous_ofReal.add (continuous_const.mul continuous_const)) hcb
  have hcontt : Continuous (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I)) :=
    Continuous.div continuous_const
      (continuous_ofReal.add (continuous_const.mul continuous_const)) hct
  have hfb : IntegrableOn (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontb.intervalIntegrable _ _)
  have hft : IntegrableOn (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontt.intervalIntegrable _ _)
  have hreb : ∀ x : ℝ, ((1 : ℂ) / (x + -T * Complex.I)).re = x / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im, one_mul, mul_one, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, neg_zero]
    field_simp
    ring
  have hret : ∀ x : ℝ, ((1 : ℂ) / (x + T * Complex.I)).re = x / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, Complex.add_im, Complex.mul_im, one_mul, mul_one,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    field_simp
    ring
  have himb : ∀ x : ℝ, ((1 : ℂ) / (x + -T * Complex.I)).im = T / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.normSq_apply, one_mul, mul_one, mul_zero, zero_mul,
      add_zero, zero_add]
    field_simp
    ring
  have himt : ∀ x : ℝ, ((1 : ℂ) / (x + T * Complex.I)).im = -T / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.normSq_apply, one_mul, mul_one,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    field_simp
    ring
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  have hifb : IntervalIntegrable (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I))
      volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hfb
  have hift : IntervalIntegrable (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I))
      volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hft
  have hreb_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I)).re =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + -T * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hifb).symm
  have hret_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I)).re =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + T * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hift).symm
  have himb_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I)).im =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + -T * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hifb).symm
  have himt_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I)).im =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + T * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hift).symm
  apply Complex.ext
  · simp only [Complex.sub_re]
    rw [hreb_integral, hret_integral]
    simp_rw [hreb, hret, sub_self]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      h2re, h2im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, mul_zero, zero_mul, sub_self]
  · simp only [Complex.sub_im]
    rw [himb_integral, himt_integral]
    simp_rw [himb, himt]
    have hneg : ∀ x : ℝ, -T / (x ^ 2 + T ^ 2) = -(T / (x ^ 2 + T ^ 2)) := by
      intro x
      ring
    simp_rw [hneg, intervalIntegral.integral_neg, integral_div_add_sq hT]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      h2re, h2im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, mul_zero, sub_self, mul_one]
    ring

open Real in
/-- Boundary integral of `1/s` over a rectangle containing `0`: `2πi`. -/
theorem boundary_rect_one_div {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I)))
      = 2 * Real.pi * Complex.I := by
  have hab : a ≤ b := le_of_lt (lt_trans ha hb)
  have hbt : 0 < b / T := div_pos hb hT
  have hat : a / T < 0 := div_neg_of_neg_of_pos ha hT
  rw [horiz_diff_one_div (ne_of_gt hT) hab,
    vertical_side_one_div (ne_of_gt hb) hT.le,
    vertical_side_one_div (ne_of_lt ha) hT.le,
    show T / b = (b / T)⁻¹ by rw [inv_div],
    show T / a = (a / T)⁻¹ by rw [inv_div],
    arctan_inv_of_pos hbt, arctan_inv_of_neg hat]
  push_cast
  ring

open Real in
/-- Rectangle boundary of `1/s` with the pole outside (`0 < a`): vanishes. -/
theorem boundary_rect_one_div_outside {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I)))
      = 0 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbt : 0 < b / T := div_pos hb hT
  have hat : 0 < a / T := div_pos ha hT
  rw [horiz_diff_one_div (ne_of_gt hT) hab,
    vertical_side_one_div (ne_of_gt hb) hT.le,
    vertical_side_one_div (ne_of_gt ha) hT.le,
    show T / b = (b / T)⁻¹ by rw [inv_div],
    show T / a = (a / T)⁻¹ by rw [inv_div],
    arctan_inv_of_pos hbt, arctan_inv_of_pos hat]
  push_cast
  ring

end Complex


/-- An axis-parallel rectangle, recorded by a pair of opposite corners.

The order of the corners determines the orientation of the displayed
boundary integral.  Degenerate rectangles are retained: their boundary
integral is zero and allowing them makes finite-chain operations cleaner. -/
structure RectilinearRectangle where
  first : ℂ
  second : ℂ

@[ext]
theorem RectilinearRectangle.ext {r s : RectilinearRectangle} (hfirst : r.first = s.first)
    (hsecond : r.second = s.second) : r = s := by
  cases r
  cases s
  simp_all

namespace RectilinearRectangle

/-- Axis-parallel rectangle specified by its real-coordinate bounds. -/
noncomputable def ofBounds (x₀ x₁ y₀ y₁ : ℝ) : RectilinearRectangle where
  first := (x₀ : ℂ) + (y₀ : ℂ) * Complex.I
  second := (x₁ : ℂ) + (y₁ : ℂ) * Complex.I

@[simp] theorem ofBounds_first_re (x₀ x₁ y₀ y₁ : ℝ) :
    (ofBounds x₀ x₁ y₀ y₁).first.re = x₀ := by simp [ofBounds]

@[simp] theorem ofBounds_first_im (x₀ x₁ y₀ y₁ : ℝ) :
    (ofBounds x₀ x₁ y₀ y₁).first.im = y₀ := by simp [ofBounds]

@[simp] theorem ofBounds_second_re (x₀ x₁ y₀ y₁ : ℝ) :
    (ofBounds x₀ x₁ y₀ y₁).second.re = x₁ := by simp [ofBounds]

@[simp] theorem ofBounds_second_im (x₀ x₁ y₀ y₁ : ℝ) :
    (ofBounds x₀ x₁ y₀ y₁).second.im = y₁ := by simp [ofBounds]

/-- The closed rectangle determined by the two opposite corners. -/
def carrier (r : RectilinearRectangle) : Set ℂ :=
  Complex.Rectangle r.first r.second

theorem convex_carrier (r : RectilinearRectangle) : Convex ℝ r.carrier := by
  have h := convex_convexHull ℝ
    ([[r.first.re, r.second.re]] ×ℂ [[r.first.im, r.second.im]])
  rw [Complex.convexHull_reProdIm,
    (convex_uIcc r.first.re r.second.re).convexHull_eq,
    (convex_uIcc r.first.im r.second.im).convexHull_eq] at h
  exact h

/-- The Banach-valued integral over the displayed oriented boundary of a
rectangle. The corner order determines the sign; for increasing real and
imaginary coordinates this is the positive orientation. This is written in
exactly the form used by Mathlib's rectangular Cauchy--Goursat theorem. -/
noncomputable def boundaryIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (r : RectilinearRectangle) (f : ℂ → E) : E :=
  (∫ x : ℝ in r.first.re..r.second.re, f (x + r.first.im * Complex.I)) -
    (∫ x : ℝ in r.first.re..r.second.re, f (x + r.second.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in r.first.im..r.second.im, f (r.second.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in r.first.im..r.second.im, f (r.first.re + y * Complex.I))

/-- Banach-valued Cauchy--Goursat on a rectangle boundary. -/
theorem boundaryIntegral_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (r : RectilinearRectangle) {f : ℂ → E}
    (hf : DifferentiableOn ℂ f r.carrier) : r.boundaryIntegral f = 0 := by
  simpa only [boundaryIntegral, carrier, Complex.Rectangle] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f r.first r.second hf

/-- Horizontal gluing of two rectangle boundary integrals.  The common
horizontal side cancels and the two vertical integrals concatenate. -/
theorem boundaryIntegral_ofBounds_horizontal_concat {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (x₀ x₁ y₀ y₁ y₂ : ℝ)
    (h₀ : Continuous fun y : ℝ ↦ f ((x₀ : ℂ) + (y : ℂ) * Complex.I))
    (h₁ : Continuous fun y : ℝ ↦ f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) :
    (ofBounds x₀ x₁ y₀ y₂).boundaryIntegral f =
      (ofBounds x₀ x₁ y₀ y₁).boundaryIntegral f +
        (ofBounds x₀ x₁ y₁ y₂).boundaryIntegral f := by
  simp only [boundaryIntegral, ofBounds_first_re, ofBounds_first_im,
    ofBounds_second_re, ofBounds_second_im]
  have hright : (∫ y : ℝ in y₀..y₂, f ((x₁ : ℂ) + y * Complex.I)) =
      (∫ y : ℝ in y₀..y₁, f ((x₁ : ℂ) + y * Complex.I)) +
        ∫ y : ℝ in y₁..y₂, f ((x₁ : ℂ) + y * Complex.I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (h₁.intervalIntegrable y₀ y₁) (h₁.intervalIntegrable y₁ y₂)).symm
  have hleft : (∫ y : ℝ in y₀..y₂, f ((x₀ : ℂ) + y * Complex.I)) =
      (∫ y : ℝ in y₀..y₁, f ((x₀ : ℂ) + y * Complex.I)) +
        ∫ y : ℝ in y₁..y₂, f ((x₀ : ℂ) + y * Complex.I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (h₀.intervalIntegrable y₀ y₁) (h₀.intervalIntegrable y₁ y₂)).symm
  rw [hright, hleft]
  have hhorizontal (y : ℝ) :
      (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ x : ℝ in x₀..x₁, f ((y : ℂ) * Complex.I + (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change f ((x : ℂ) + (y : ℂ) * Complex.I) =
      f ((y : ℂ) * Complex.I + (x : ℂ))
    rw [add_comm]
  simp_rw [hhorizontal]
  simp only [smul_add]
  abel_nf

/-- Vertical gluing of two rectangle boundary integrals.  The common vertical
side cancels and the two horizontal integrals concatenate. -/
theorem boundaryIntegral_ofBounds_vertical_concat {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (x₀ x₁ x₂ y₀ y₁ : ℝ)
    (h₀ : Continuous fun x : ℝ ↦ f ((x : ℂ) + (y₀ : ℂ) * Complex.I))
    (h₁ : Continuous fun x : ℝ ↦ f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) :
    (ofBounds x₀ x₂ y₀ y₁).boundaryIntegral f =
      (ofBounds x₀ x₁ y₀ y₁).boundaryIntegral f +
        (ofBounds x₁ x₂ y₀ y₁).boundaryIntegral f := by
  simp only [boundaryIntegral, ofBounds_first_re, ofBounds_first_im,
    ofBounds_second_re, ofBounds_second_im]
  have hbottom : (∫ x : ℝ in x₀..x₂,
      f ((x : ℂ) + (y₀ : ℂ) * Complex.I)) =
      (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + (y₀ : ℂ) * Complex.I)) +
        ∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₀ : ℂ) * Complex.I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (h₀.intervalIntegrable x₀ x₁) (h₀.intervalIntegrable x₁ x₂)).symm
  have htop : (∫ x : ℝ in x₀..x₂,
      f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) =
      (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) +
        ∫ x : ℝ in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (h₁.intervalIntegrable x₀ x₁) (h₁.intervalIntegrable x₁ x₂)).symm
  rw [hbottom, htop]
  have hhorizontal (a b y : ℝ) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ x : ℝ in a..b, f ((y : ℂ) * Complex.I + (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change f ((x : ℂ) + (y : ℂ) * Complex.I) =
      f ((y : ℂ) * Complex.I + (x : ℂ))
    rw [add_comm]
  simp_rw [hhorizontal]
  abel_nf

/-- The Cauchy kernel has zero boundary integral when its pole is outside
the closed rectangle. -/
theorem boundaryIntegral_inv_sub_eq_zero_of_not_mem_carrier
    (r : RectilinearRectangle) {w : ℂ} (hw : w ∉ r.carrier) :
    r.boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) = 0 := by
  apply r.boundaryIntegral_eq_zero
  intro z hz
  exact ((differentiableAt_id.sub_const w).inv
    (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))).differentiableWithinAt

theorem boundaryIntegral_congr_of_eqOn_carrier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (r : RectilinearRectangle) {f g : ℂ → E} (hfg : Set.EqOn f g r.carrier) :
    r.boundaryIntegral f = r.boundaryIntegral g := by
  have hbottom : (∫ x : ℝ in r.first.re..r.second.re,
      f (x + r.first.im * Complex.I)) =
      ∫ x : ℝ in r.first.re..r.second.re,
        g (x + r.first.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hfg
    rw [carrier, Complex.Rectangle, Complex.mem_reProdIm]
    simpa using (show
      x ∈ [[r.first.re, r.second.re]] ∧
        r.first.im ∈ [[r.first.im, r.second.im]] from ⟨hx, left_mem_uIcc⟩)
  have htop : (∫ x : ℝ in r.first.re..r.second.re,
      f (x + r.second.im * Complex.I)) =
      ∫ x : ℝ in r.first.re..r.second.re,
        g (x + r.second.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hfg
    rw [carrier, Complex.Rectangle, Complex.mem_reProdIm]
    simpa using (show
      x ∈ [[r.first.re, r.second.re]] ∧
        r.second.im ∈ [[r.first.im, r.second.im]] from ⟨hx, right_mem_uIcc⟩)
  have hright : (∫ y : ℝ in r.first.im..r.second.im,
      f (r.second.re + y * Complex.I)) =
      ∫ y : ℝ in r.first.im..r.second.im,
        g (r.second.re + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply hfg
    rw [carrier, Complex.Rectangle, Complex.mem_reProdIm]
    simpa using (show
      r.second.re ∈ [[r.first.re, r.second.re]] ∧
        y ∈ [[r.first.im, r.second.im]] from ⟨right_mem_uIcc, hy⟩)
  have hleft : (∫ y : ℝ in r.first.im..r.second.im,
      f (r.first.re + y * Complex.I)) =
      ∫ y : ℝ in r.first.im..r.second.im,
        g (r.first.re + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply hfg
    rw [carrier, Complex.Rectangle, Complex.mem_reProdIm]
    simpa using (show
      r.first.re ∈ [[r.first.re, r.second.re]] ∧
        y ∈ [[r.first.im, r.second.im]] from ⟨left_mem_uIcc, hy⟩)
  simp only [boundaryIntegral]
  rw [hbottom, htop, hright, hleft]

/-- The boundary integral of the Cauchy kernel on a rectangle centered
vertically at the origin is its residue, provided the origin is strictly
between the two vertical sides. -/
theorem boundaryIntegral_ofBounds_inv_eq_two_pi_mul_I {a b T : ℝ}
    (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (ofBounds a b (-T) T).boundaryIntegral (fun z : ℂ ↦ z⁻¹) =
      (2 * Real.pi : ℂ) * Complex.I := by
  simp only [boundaryIntegral, ofBounds_first_re, ofBounds_first_im,
    ofBounds_second_re, ofBounds_second_im, Complex.ofReal_neg, smul_eq_mul]
  have hp := Complex.boundary_rect_one_div ha hb hT
  simp only [one_div] at hp
  linear_combination hp

/-- Translating the rectangle and pole by the same amount reduces the
Cauchy-kernel boundary integral to a pole at the origin. -/
theorem boundaryIntegral_ofBounds_inv_sub_eq_translate
    (x₀ x₁ y₀ y₁ : ℝ) (w : ℂ) :
    (ofBounds x₀ x₁ y₀ y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) =
      (ofBounds (x₀ - w.re) (x₁ - w.re) (y₀ - w.im) (y₁ - w.im)).boundaryIntegral
        (fun z : ℂ ↦ z⁻¹) := by
  have hpoint (x y : ℝ) :
      (((x : ℂ) + (y : ℂ) * Complex.I) - w)⁻¹ =
        (((x - w.re : ℝ) : ℂ) + ((y - w.im : ℝ) : ℂ) * Complex.I)⁻¹ := by
    congr 1
    apply Complex.ext <;> simp
  have hx (y : ℝ) :
      (∫ x : ℝ in x₀..x₁,
          (((x - w.re : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹) =
        ∫ x : ℝ in (x₀ - w.re)..(x₁ - w.re),
          ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ := by
    simpa using intervalIntegral.integral_comp_sub_right
      (fun x : ℝ ↦ ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹) w.re
  have hy (x : ℝ) :
      (∫ y : ℝ in y₀..y₁,
          ((x : ℂ) + ((y - w.im : ℝ) : ℂ) * Complex.I)⁻¹) =
        ∫ y : ℝ in (y₀ - w.im)..(y₁ - w.im),
          ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ := by
    simpa using intervalIntegral.integral_comp_sub_right
      (fun y : ℝ ↦ ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹) w.im
  simp only [boundaryIntegral, ofBounds_first_re, ofBounds_first_im,
    ofBounds_second_re, ofBounds_second_im]
  simp_rw [hpoint]
  rw [hx, hx, hy, hy]

/-- A positively oriented rectangle has Cauchy-kernel boundary integral
`2πi` at every point of its open interior. -/
theorem boundaryIntegral_ofBounds_inv_sub_eq_two_pi_mul_I
    {x₀ x₁ y₀ y₁ : ℝ} {w : ℂ}
    (hx₀ : x₀ < w.re) (hx₁ : w.re < x₁)
    (hy₀ : y₀ < w.im) (hy₁ : w.im < y₁) :
    (ofBounds x₀ x₁ y₀ y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) =
      (2 * Real.pi : ℂ) * Complex.I := by
  let T : ℝ := min (w.im - y₀) (y₁ - w.im)
  have hT : 0 < T := lt_min (sub_pos.2 hy₀) (sub_pos.2 hy₁)
  let y₀' : ℝ := w.im - T
  let y₁' : ℝ := w.im + T
  have hy₀le : y₀ ≤ y₀' := by
    dsimp [y₀', T]
    linarith [min_le_left (w.im - y₀) (y₁ - w.im)]
  have hy₀' : y₀' < w.im := by simp [y₀', hT]
  have hy₁le : y₁' ≤ y₁ := by
    dsimp [y₁', T]
    linarith [min_le_right (w.im - y₀) (y₁ - w.im)]
  have hy₁' : w.im < y₁' := by simp [y₁', hT]
  have hvertical (x : ℝ) (hx : x ≠ w.re) :
      Continuous fun y : ℝ ↦
        (((x : ℂ) + (y : ℂ) * Complex.I) - w)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro y h
    apply hx
    have hre := congrArg Complex.re h
    exact sub_eq_zero.mp (by simpa using hre)
  have hwlow : w ∉ (ofBounds x₀ x₁ y₀ y₀').carrier := by
    intro hw
    have hxorder : x₀ ≤ x₁ := hx₀.le.trans hx₁.le
    have hw' : w.re ∈ Icc x₀ x₁ ∧ w.im ∈ Icc y₀ y₀' := by
      simpa only [carrier, Complex.Rectangle, ofBounds_first_re, ofBounds_first_im,
        ofBounds_second_re, ofBounds_second_im, Complex.mem_reProdIm,
        uIcc_of_le hxorder, uIcc_of_le hy₀le] using hw
    exact (not_le_of_gt hy₀') hw'.2.2
  have hwup : w ∉ (ofBounds x₀ x₁ y₁' y₁).carrier := by
    intro hw
    have hxorder : x₀ ≤ x₁ := hx₀.le.trans hx₁.le
    have hw' : w.re ∈ Icc x₀ x₁ ∧ w.im ∈ Icc y₁' y₁ := by
      simpa only [carrier, Complex.Rectangle, ofBounds_first_re, ofBounds_first_im,
        ofBounds_second_re, ofBounds_second_im, Complex.mem_reProdIm,
        uIcc_of_le hxorder, uIcc_of_le hy₁le] using hw
    exact (not_le_of_gt hy₁') hw'.2.1
  have hlow :
      (ofBounds x₀ x₁ y₀ y₀').boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) = 0 :=
    boundaryIntegral_inv_sub_eq_zero_of_not_mem_carrier _ hwlow
  have hup :
      (ofBounds x₀ x₁ y₁' y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) = 0 :=
    boundaryIntegral_inv_sub_eq_zero_of_not_mem_carrier _ hwup
  have hmid :
      (ofBounds x₀ x₁ y₀' y₁').boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) =
        (2 * Real.pi : ℂ) * Complex.I := by
    rw [boundaryIntegral_ofBounds_inv_sub_eq_translate]
    simpa [y₀', y₁'] using
      boundaryIntegral_ofBounds_inv_eq_two_pi_mul_I
        (sub_neg.mpr hx₀) (sub_pos.mpr hx₁) hT
  calc
    (ofBounds x₀ x₁ y₀ y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) =
        (ofBounds x₀ x₁ y₀ y₀').boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) +
          (ofBounds x₀ x₁ y₀' y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) :=
      boundaryIntegral_ofBounds_horizontal_concat _ x₀ x₁ y₀ y₀' y₁
        (hvertical x₀ hx₀.ne) (hvertical x₁ hx₁.ne')
    _ = (ofBounds x₀ x₁ y₀ y₀').boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) +
          ((ofBounds x₀ x₁ y₀' y₁').boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) +
            (ofBounds x₀ x₁ y₁' y₁).boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹)) := by
      rw [boundaryIntegral_ofBounds_horizontal_concat _ x₀ x₁ y₀' y₁' y₁
        (hvertical x₀ hx₀.ne) (hvertical x₁ hx₁.ne')]
    _ = (2 * Real.pi : ℂ) * Complex.I := by rw [hlow, hmid, hup, zero_add, add_zero]

end RectilinearRectangle

/-- A finite oriented rectilinear cycle, represented as an integer formal sum
of displayed oriented rectangle boundaries. Negative coefficients reverse
orientation. -/
abbrev RectilinearCycle := RectilinearRectangle →₀ ℤ

namespace RectilinearCycle

/-- The cycle consisting of one rectangle boundary with its displayed
corner-order orientation. -/
noncomputable def ofRectangle (r : RectilinearRectangle) : RectilinearCycle :=
  Finsupp.single r 1

/-- The Banach-valued contour integral of a finite rectilinear cycle. -/
noncomputable def integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (Γ : RectilinearCycle) (f : ℂ → E) : E :=
  Γ.sum fun r n ↦ n • r.boundaryIntegral f

@[simp]
theorem integral_ofRectangle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (r : RectilinearRectangle) (f : ℂ → E) :
    integral (ofRectangle r) f = r.boundaryIntegral f := by
  simp [integral, ofRectangle]

@[simp]
theorem integral_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) :
    integral (0 : RectilinearCycle) f = 0 := by
  simp [integral]

/-- Contour integration is additive in the rectilinear cycle. -/
theorem integral_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (Γ Λ : RectilinearCycle) (f : ℂ → E) :
    integral (Γ + Λ) f = integral Γ f + integral Λ f := by
  unfold integral
  apply Finsupp.sum_add_index'
  · intro r
    simp
  · intro r m n
    simp [add_zsmul]

/-- Reversing a rectilinear cycle negates its contour integral. -/
theorem integral_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (Γ : RectilinearCycle) (f : ℂ → E) :
    integral (-Γ) f = -integral Γ f := by
  apply eq_neg_of_add_eq_zero_left
  rw [← integral_add, neg_add_cancel, integral_zero]

/-- Contour integration turns subtraction of cycles into subtraction in the
Banach-space codomain. -/
theorem integral_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (Γ Λ : RectilinearCycle) (f : ℂ → E) :
    integral (Γ - Λ) f = integral Γ f - integral Λ f := by
  rw [sub_eq_add_neg, integral_add, integral_neg, sub_eq_add_neg]

/-- Contour integration against a fixed function, bundled as an additive
homomorphism in the rectilinear cycle. -/
noncomputable def integralAddHom {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) : RectilinearCycle →+ E where
  toFun Γ := Γ.integral f
  map_zero' := integral_zero f
  map_add' Γ Λ := integral_add Γ Λ f

@[simp]
theorem integralAddHom_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (Γ : RectilinearCycle) :
    integralAddHom f Γ = Γ.integral f := rfl

/-- A rectangle filling is supported in `G` when every rectangle occurring
with nonzero coefficient is contained in `G`. -/
def FillingSupportedIn (Γ : RectilinearCycle) (G : Set ℂ) : Prop :=
  ∀ r ∈ Γ.support, r.carrier ⊆ G

theorem integral_congr_of_fillingSupportedIn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Γ : RectilinearCycle} {G : Set ℂ} {f g : ℂ → E}
    (hΓ : Γ.FillingSupportedIn G) (hfg : Set.EqOn f g G) :
    Γ.integral f = Γ.integral g := by
  unfold integral
  apply Finsupp.sum_congr
  intro r hr
  rw [r.boundaryIntegral_congr_of_eqOn_carrier (hfg.mono (hΓ r hr))]

/-- Cauchy--Goursat for a finite rectilinear cycle whose rectangle filling is
contained in the domain of differentiability. -/
theorem integral_eq_zero_of_fillingSupportedIn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Γ : RectilinearCycle} {G : Set ℂ} {f : ℂ → E}
    (hΓ : Γ.FillingSupportedIn G) (hf : DifferentiableOn ℂ f G) :
    Γ.integral f = 0 := by
  classical
  unfold integral
  calc
    Γ.sum (fun r n ↦ n • r.boundaryIntegral f) = Γ.sum (fun _ _ ↦ (0 : E)) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [r.boundaryIntegral_eq_zero (hf.mono (hΓ r hr)), smul_zero]
    _ = 0 := by simp

/-- A present rectangular homology relation: the difference of two
cycles has a rectangle filling contained in `G`. -/
def HomologousIn (Γ Λ : RectilinearCycle) (G : Set ℂ) : Prop :=
  (Γ - Λ).FillingSupportedIn G

/-- Homologous rectilinear cycles have the same integral for a function
differentiable on the filling domain. -/
theorem integral_eq_of_homologousIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {Γ Λ : RectilinearCycle}
    {G : Set ℂ} {f : ℂ → E} (hΓΛ : Γ.HomologousIn Λ G)
    (hf : DifferentiableOn ℂ f G) : Γ.integral f = Λ.integral f := by
  rw [← sub_eq_zero, ← integral_sub]
  exact integral_eq_zero_of_fillingSupportedIn hΓΛ hf

/-- The analytic index expression of a rectilinear cycle about `w`.

Lean's inverse is total, so the definition also has a value when `w` lies
on a presented rectangle boundary; no geometric winding-number claim is made
there. -/
noncomputable def index (Γ : RectilinearCycle) (w : ℂ) : ℂ :=
  ((2 * Real.pi : ℂ) * Complex.I)⁻¹ *
    Γ.integral (fun z : ℂ ↦ (z - w)⁻¹)

theorem index_add (Γ Λ : RectilinearCycle) (w : ℂ) :
    index (Γ + Λ) w = index Γ w + index Λ w := by
  simp [index, integral_add, mul_add]

theorem index_neg (Γ : RectilinearCycle) (w : ℂ) :
    index (-Γ) w = -index Γ w := by
  simp [index, integral_neg]

theorem index_sub (Γ Λ : RectilinearCycle) (w : ℂ) :
    index (Γ - Λ) w = index Γ w - index Λ w := by
  simp [index, integral_sub, mul_sub]

/-- Winding index at a fixed point, bundled as an additive homomorphism in
the rectilinear cycle. -/
noncomputable def indexAddHom (w : ℂ) : RectilinearCycle →+ ℂ where
  toFun Γ := Γ.index w
  map_zero' := by simp [index]
  map_add' Γ Λ := index_add Γ Λ w

@[simp]
theorem indexAddHom_apply (w : ℂ) (Γ : RectilinearCycle) :
    indexAddHom w Γ = Γ.index w := rfl

@[simp]
theorem index_ofRectangle (r : RectilinearRectangle) (w : ℂ) :
    index (ofRectangle r) w = ((2 * Real.pi : ℂ) * Complex.I)⁻¹ *
      r.boundaryIntegral (fun z : ℂ ↦ (z - w)⁻¹) := by
  simp [index]

/-- A rectangle has winding index zero about every point outside its closed
carrier. -/
theorem index_ofRectangle_eq_zero_of_not_mem_carrier
    (r : RectilinearRectangle) {w : ℂ} (hw : w ∉ r.carrier) :
    index (ofRectangle r) w = 0 := by
  rw [index_ofRectangle, r.boundaryIntegral_eq_zero]
  · simp
  · intro z hz
    exact ((differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))).differentiableWithinAt

@[simp]
theorem index_zero (w : ℂ) : index (0 : RectilinearCycle) w = 0 := by
  simp [index]

end RectilinearCycle
