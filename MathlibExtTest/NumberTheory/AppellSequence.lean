module

public import MathlibExt.NumberTheory.AppellSequence

open MetaMathlibExt

private noncomputable def monomialSeq : ℕ → Polynomial ℚ :=
  fun n => Polynomial.X ^ n

private noncomputable def zeroSeq : ℕ → Polynomial ℚ :=
  fun _ => 0

private theorem monomial_isAppell : IsAppellSequence monomialSeq := by
  constructor
  · intro n
    simp [monomialSeq]
  · intro n
    simp [monomialSeq]

private theorem deg_check0 : (monomialSeq 0).degree = 0 :=
  monomial_isAppell.1 0

private theorem deg_check1 : (monomialSeq 1).degree = 1 :=
  monomial_isAppell.1 1

private theorem deriv_check0 :
    Polynomial.derivative (monomialSeq 1) =
      Polynomial.C ((0 + 1 : ℕ) : ℚ) * monomialSeq 0 :=
  monomial_isAppell.2 0

private theorem deriv_check1 :
    Polynomial.derivative (monomialSeq 2) =
      Polynomial.C ((1 + 1 : ℕ) : ℚ) * monomialSeq 1 :=
  monomial_isAppell.2 1

private theorem zero_not_appell : ¬IsAppellSequence zeroSeq := by
  intro h
  have h0 := h.1 0
  simp [zeroSeq] at h0
