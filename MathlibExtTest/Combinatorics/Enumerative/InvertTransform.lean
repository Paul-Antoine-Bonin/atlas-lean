import MathlibExt.Combinatorics.Enumerative.InvertTransform

open MetaMathlibExt

private theorem invertTransform_zero_0 : invertTransform (fun _ => (0 : ℤ)) 0 = 0 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

private theorem invertTransform_zero_1 : invertTransform (fun _ => (0 : ℤ)) 1 = 0 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

private theorem invertTransform_one_0 : invertTransform (fun _ => (1 : ℤ)) 0 = 1 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

private theorem invertTransform_one_1 : invertTransform (fun _ => (1 : ℤ)) 1 = 2 := by
  have h0 := invertTransform_one_0
  change PowerSeries.coeff 1
    ((1 - PowerSeries.X * PowerSeries.mk fun _ => (1 : ℤ)).invOfUnit 1) = 1 at h0
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal, h0]

example (a : ℕ → ℤ) :
    (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
  exact invertTransform_spec a
