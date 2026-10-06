module

public import MathlibExt.Analysis.PerronKernel

/-!
# Truncated Perron kernel API checks

Focused checks for the exported kernel, rectangle-boundary identities, and
all-cases error estimate.
-/

@[expose] public section

open Complex intervalIntegral

example (y c T : ℝ) :
    PerronKernel.perronKernel y c T =
      (1 / (2 * Real.pi)) * ∫ t : ℝ in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) :=
  rfl

example {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * I))
      + I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * I)))
      = 2 * Real.pi * I :=
  PerronKernel.boundary_rect_one_div ha hb hT

example {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * I))
      + I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * I)))
      = 0 :=
  PerronKernel.boundary_rect_one_div_outside ha hab hT

example {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖PerronKernel.perronKernel y c T - (if 1 < y then (1 : ℂ) else 0)‖ ≤
      Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi :=
  PerronKernel.perron_bound hy hy1 hc hT
