module

import MathlibExt.Analysis.Fourier.FourierLaplace

@[expose] public section

open MeasureTheory
namespace FourierTest

private noncomputable def compactlySupportedExample : ℝ → ℂ :=
  Set.Icc (-1 : ℝ) 1 |>.indicator fun _ => 1

private theorem compactlySupportedExample_integrable : Integrable compactlySupportedExample := by
  exact IntegrableOn.integrable_indicator
    (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc

private theorem compactlySupportedExample_hasCompactSupport :
    HasCompactSupport compactlySupportedExample := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  rw [compactlySupportedExample, Set.indicator_apply, ite_eq_right hx]

example (f : ℝ → ℂ) (r : ℝ) :
    Fourier.fourierLaplace f r =
      Fourier.fourierIntegral Real.fourierChar volume f r :=
  Fourier.fourierLaplace_ofReal f r

example (f : ℝ → ℂ) : Fourier.fourierLaplace f 0 = ∫ x, f x := by
  simp

example (z : ℂ) : Fourier.fourierLaplace 0 z = 0 := by
  simp

example : Differentiable ℂ (Fourier.fourierLaplace compactlySupportedExample) :=
  Fourier.differentiable_fourierLaplace compactlySupportedExample_integrable
    compactlySupportedExample_hasCompactSupport

example (z : ℂ) :
    HasDerivAt (Fourier.fourierLaplace compactlySupportedExample)
      (∫ x : ℝ, compactlySupportedExample x *
        ((-2 * (Real.pi : ℂ) * Complex.I * x) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * x * z))) z :=
  Fourier.hasDerivAt_fourierLaplace compactlySupportedExample_integrable
    compactlySupportedExample_hasCompactSupport z

end FourierTest
