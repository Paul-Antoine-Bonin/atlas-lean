/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.NormalConvergence

/-!
# Tests for normal convergence APIs

Exercises the normal-convergence API on a concrete nonzero complex one-term
series, including absolute, uniform, and locally uniform convergence and
termwise differentiation.
-/

@[expose] public section

open Complex MeasureTheory Topology Set Filter

namespace N329Test

/-- Concrete nonzero complex one-term series used for testing. -/
def complexOneTermSeries : Nat → Complex → Complex :=
  fun n _ => if n = 0 then 1 else 0

/-- The sup norm of the concrete series has exactly one nonzero term. -/
theorem complexOneTermSeries_supNormOn (n : Nat) :
    supNormOn (complexOneTermSeries n) (Set.univ : Set Complex) =
      if n = 0 then (1 : ENNReal) else 0 := by
  have : Nonempty ↥((Set.univ : Set Complex)) := ⟨⟨0, Set.mem_univ _⟩⟩
  unfold supNormOn
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl]
    have hbody : ∀ x : ↥((Set.univ : Set Complex)),
        ENNReal.ofReal ‖complexOneTermSeries 0 x‖ = 1 := by
      intro x
      simp [complexOneTermSeries]
    simp only [hbody]
    exact iSup_const
  · rw [ite_eq_right hn]
    have hbody : ∀ x : ↥((Set.univ : Set Complex)),
        ENNReal.ofReal ‖complexOneTermSeries n x‖ = 0 := by
      intro x
      simp [complexOneTermSeries, hn]
    simp only [hbody]
    exact iSup_const

theorem complexOneTermSeries_convergesNormallyOn :
    ConvergesNormallyOn complexOneTermSeries Set.univ := by
  unfold ConvergesNormallyOn
  rw [tsum_congr complexOneTermSeries_supNormOn,
    tsum_eq_single 0 (fun b hb => ite_eq_right hb), ite_eq_left rfl]
  exact ENNReal.one_ne_top

theorem complexOneTermSeries_convergesLocallyNormallyOn :
    ConvergesLocallyNormallyOn complexOneTermSeries Set.univ := by
  intro z _
  exact ⟨Set.univ, Filter.univ_mem, by simpa using
    complexOneTermSeries_convergesNormallyOn⟩

theorem complexOneTermSeries_differentiableOn (n : Nat) :
    DifferentiableOn Complex (complexOneTermSeries n) Set.univ := by
  by_cases hn : n = 0
  · subst hn
    have hfun : complexOneTermSeries 0 = fun _ => 1 := by
      funext z
      simp [complexOneTermSeries]
    rw [hfun]
    exact differentiableOn_const 1
  · have hfun : complexOneTermSeries n = fun _ => 0 := by
      funext z
      simp [complexOneTermSeries, hn]
    rw [hfun]
    exact differentiableOn_const 0

/-- Direct example invoking `summable_toReal_supNormOn`. -/
example : Summable (fun n => (supNormOn (complexOneTermSeries n) Set.univ).toReal) :=
  complexOneTermSeries_convergesNormallyOn.summable_toReal_supNormOn

/-- Normal convergence gives pointwise absolute convergence. -/
example (z : Complex) : Summable (fun n => ‖complexOneTermSeries n z‖) :=
  complexOneTermSeries_convergesNormallyOn.summable_norm (Set.mem_univ z)

/-- Local normal convergence gives pointwise absolute convergence. -/
example (z : Complex) : Summable (fun n => ‖complexOneTermSeries n z‖) :=
  complexOneTermSeries_convergesLocallyNormallyOn.summable_norm (Set.mem_univ z)

/-- Direct example invoking `tendstoUniformlyOn_tsum_nat`. -/
example :
    TendstoUniformlyOn
      (fun k z => ∑ n ∈ Finset.range k, complexOneTermSeries n z)
      (fun z => ∑' n, complexOneTermSeries n z) Filter.atTop Set.univ :=
  complexOneTermSeries_convergesNormallyOn.tendstoUniformlyOn_tsum_nat

/-- Direct example invoking `tendstoLocallyUniformlyOn_tsum_nat`. -/
example :
    TendstoLocallyUniformlyOn
      (fun k z => ∑ n ∈ Finset.range k, complexOneTermSeries n z)
      (fun z => ∑' n, complexOneTermSeries n z) Filter.atTop Set.univ :=
  complexOneTermSeries_convergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat

/-- Exercise the `deriv` theorem on the concrete series. -/
example :
    ConvergesLocallyNormallyOn
      (fun n w => deriv (complexOneTermSeries n) w) Set.univ :=
  complexOneTermSeries_convergesLocallyNormallyOn.deriv isOpen_univ
    complexOneTermSeries_differentiableOn

/-- Exercise the `hasDerivAt_tsum` theorem on the concrete series. -/
example (z : Complex) :
    HasDerivAt (fun w => ∑' n, complexOneTermSeries n w)
      (∑' n, deriv (complexOneTermSeries n) z) z :=
  complexOneTermSeries_convergesLocallyNormallyOn.hasDerivAt_tsum isOpen_univ
    complexOneTermSeries_differentiableOn (Set.mem_univ z)

/-- The concrete series sums to one everywhere. -/
example (z : Complex) : (∑' n, complexOneTermSeries n z) = 1 := by
  simp [complexOneTermSeries, tsum_eq_single 0]

/-- The derivative theorem remains polymorphic in the complex normed codomain. -/
example :
    ConvergesLocallyNormallyOn
      (fun n z => deriv ((0 : Nat → Complex → Complex × Complex) n) z) Set.univ := by
  have hzero : ConvergesLocallyNormallyOn
      (0 : Nat → Complex → Complex × Complex) Set.univ :=
    convergesLocallyNormallyOn_zero Set.univ
  apply hzero.deriv isOpen_univ
  intro n
  change DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ × ℂ)) Set.univ
  exact differentiableOn_const _

end N329Test
