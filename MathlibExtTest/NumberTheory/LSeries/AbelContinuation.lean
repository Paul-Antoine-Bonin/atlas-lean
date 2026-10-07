/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.AbelContinuation

@[expose] public section

/-!
# Tests for the Abel continuation

Zero, one-point finite-support, and alternating examples: each has `O(n ^ 0)`
partial sums, so the continuation is holomorphic on `0 < s.re` and ordered
Dirichlet partial sums converge to it there with no summability assumed.
The alternating example additionally exercises absolute `LSeriesSummable`
at `1 < s.re` and agreement of the continuation with `LSeries` there. Every
`LSeriesSummable` check below is absolute summability; no conditional
convergence is claimed.
-/

namespace AbelContinuationTest

open Filter Asymptotics Topology

/-- Partial sums of the zero sequence are `O(n ^ 0)`. -/
theorem zero_isBigO :
    (fun n => abelPartialSum (fun _ => (0 : ℂ)) n) =O[atTop]
      fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
  simp only [abelPartialSum, Finset.sum_const_zero]
  exact Asymptotics.isBigO_zero _ _

-- The continuation of the zero sequence vanishes.
example (s : ℂ) : abelContinuation (fun _ => (0 : ℂ)) s = 0 := by
  simp [abelContinuation, abelSummatory, abelPartialSum]

-- Pointwise differentiability for the zero sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ (abelContinuation (fun _ => (0 : ℂ))) s :=
  differentiableAt_abelContinuation _ hs zero_isBigO

-- Set-level analyticity for the zero sequence.
example : AnalyticOn ℂ (abelContinuation (fun _ => (0 : ℂ))) {s | (0 : ℝ) < s.re} :=
  analyticOn_abelContinuation _ zero_isBigO

-- Agreement with `LSeries` for the zero sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) (hS : LSeriesSummable (fun _ => (0 : ℂ)) s) :
    abelContinuation (fun _ => (0 : ℂ)) s = LSeries (fun _ => (0 : ℂ)) s :=
  abelContinuation_eq_LSeries _ le_rfl hs hS zero_isBigO

-- Ordered partial sums converge for the zero sequence, with no summability.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term (fun _ => (0 : ℂ)) s n)
      atTop (𝓝 (abelContinuation (fun _ => (0 : ℂ)) s)) :=
  tendsto_abelContinuation_Icc _ hs zero_isBigO

/-- A single-point sequence: partial sums are `0` below `1` and `1` above. -/
theorem partialSum_single (n : ℕ) :
    abelPartialSum (fun n => if n = 1 then (1 : ℂ) else 0) n =
      if 1 ≤ n then 1 else 0 := by
  simp only [abelPartialSum]
  rw [Finset.sum_ite_eq' _ 1 _]
  simp [Finset.mem_Icc]

/-- Partial sums of the single-point sequence are `O(n ^ 0)`. -/
theorem single_isBigO :
    (fun n => abelPartialSum (fun n => if n = 1 then (1 : ℂ) else 0) n) =O[atTop]
      fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  rw [partialSum_single]
  split_ifs with h <;> simp [Real.rpow_zero]

-- Pointwise differentiability for the single-point sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ
      (abelContinuation (fun n => if n = 1 then (1 : ℂ) else 0)) s :=
  differentiableAt_abelContinuation _ hs single_isBigO

-- Set-level analyticity for the single-point sequence.
example : AnalyticOn ℂ
    (abelContinuation (fun n => if n = 1 then (1 : ℂ) else 0))
    {s | (0 : ℝ) < s.re} :=
  analyticOn_abelContinuation _ single_isBigO

-- Ordered partial sums converge for the single-point sequence, with no
-- summability assumed.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
      LSeries.term (fun n => if n = 1 then (1 : ℂ) else 0) s n)
      atTop (𝓝 (abelContinuation
        (fun n => if n = 1 then (1 : ℂ) else 0) s)) :=
  tendsto_abelContinuation_Icc _ hs single_isBigO

/-- The alternating sequence. -/
noncomputable def alt : ℕ → ℂ := fun n => (-1) ^ n

/-- Geometric-sum identity for the alternating partial sums. -/
theorem alt_geom (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i) * ((-1 : ℂ) - 1) =
      (-1) ^ (n + 1) - 1 :=
  geom_sum_mul (-1) (n + 1)

/-- Peeling off the `k = 0` term relates the geometric sum to `abelPartialSum`. -/
theorem alt_peel (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i) = 1 + abelPartialSum alt n := by
  have h1 : Finset.range (n + 1) = Finset.Icc 0 n := by
    rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero n), Nat.add_sub_cancel]
  have h2 : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)).symm
  rw [h1, h2, Finset.sum_insert (by simp)]
  simp [alt, abelPartialSum]

/-- Closed form for the alternating partial sums. -/
theorem alt_closed (n : ℕ) :
    abelPartialSum alt n = (((-1 : ℂ) ^ (n + 1) + 1) / (-2)) := by
  have hS := alt_geom n
  rw [alt_peel n] at hS
  have h2ne : (-2 : ℂ) ≠ 0 := by norm_num
  rw [eq_div_iff h2ne]
  linear_combination hS

/-- The alternating partial sums are uniformly bounded by `1`. -/
theorem alt_bound (n : ℕ) : ‖abelPartialSum alt n‖ ≤ 1 := by
  rw [alt_closed n]
  have hnum : ‖(-1 : ℂ) ^ (n + 1) + 1‖ ≤ 2 := by
    calc ‖(-1 : ℂ) ^ (n + 1) + 1‖ ≤ ‖(-1 : ℂ) ^ (n + 1)‖ + ‖(1 : ℂ)‖ :=
          norm_add_le _ _
      _ = 2 := by simp [norm_pow, one_add_one_eq_two]
  have hden : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [norm_div, hden, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa using hnum

/-- Partial sums of the alternating sequence are `O(n ^ 0)`. -/
theorem alt_isBigO :
    (fun n => abelPartialSum alt n) =O[atTop]
      fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [Real.rpow_zero, norm_one, mul_one]
  exact alt_bound n

/-- Pointwise bound for absolute convergence of the alternating series. -/
theorem alt_pointwise_isBigO :
    alt =O[atTop] fun n => ((n : ℝ) ^ ((1 : ℝ) - 1) : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [sub_self]
  have h1 : ‖alt n‖ = 1 := by simp [alt, norm_pow]
  rw [h1]
  simp [Real.rpow_zero]

-- The alternating series is absolutely summable at `1 < s.re`.
-- (`LSeriesSummable` is absolute summability throughout; no conditional
-- convergence is claimed here.)
example {s : ℂ} (hs : (1 : ℝ) < s.re) : LSeriesSummable alt s :=
  LSeriesSummable_of_isBigO_rpow hs alt_pointwise_isBigO

-- Pointwise differentiability for the alternating sequence.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    DifferentiableAt ℂ (abelContinuation alt) s :=
  differentiableAt_abelContinuation _ hs alt_isBigO

-- Agreement with `LSeries` for the alternating sequence at `1 < s.re`.
example {s : ℂ} (hs : (1 : ℝ) < s.re) :
    abelContinuation alt s = LSeries alt s :=
  abelContinuation_eq_LSeries _ le_rfl (zero_lt_one.trans hs)
    (LSeriesSummable_of_isBigO_rpow hs alt_pointwise_isBigO) alt_isBigO

-- Ordered partial sums converge to the continuation for the alternating
-- sequence on `0 < s.re`, with no summability assumed.
example {s : ℂ} (hs : (0 : ℝ) < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term alt s n) atTop
      (𝓝 (abelContinuation alt s)) :=
  tendsto_abelContinuation_Icc _ hs alt_isBigO

end AbelContinuationTest
