module

public import MathlibExt.NumberTheory.QRDowlingPolynomial

open MetaMathlibExt

private theorem test_poly_n0 :
    qrDowlingPolynomial (R := ℕ) (fun _ k => k + 1) 0 = Polynomial.C 1 := by
  simp [qrDowlingPolynomial]

private theorem test_zero_family :
    qrDowlingPolynomial (R := ℕ) (fun _ _ => 0) 2 = 0 := by
  simp [qrDowlingPolynomial]

private theorem test_poly_n1_boundary :
    qrDowlingPolynomial (R := ℕ) (fun _ k => if k = 1 then 1 else 0) 1 =
      Polynomial.X := by
  simp [qrDowlingPolynomial]

private theorem test_number_n0 :
    qrDowlingNumber (R := ℕ) (fun _ k => k + 1) 0 = 1 := by
  simp [qrDowlingNumber_eq_sum]

example (W : ℕ → ℕ → ℕ) (n : ℕ) :
    qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k :=
  qrDowlingNumber_eq_sum W n
