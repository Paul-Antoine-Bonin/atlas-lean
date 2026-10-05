module

public import MathlibExt.NumberTheory.NoncentralTannyDowlingPolynomial

open MetaMathlibExt

variable (m a : ℤ)

private theorem w00 : noncentralWhitneySecond m a 0 0 = 1 := by
  simp [noncentralWhitneySecond]

private theorem w01 : noncentralWhitneySecond m a 0 1 = 0 := by
  simp [noncentralWhitneySecond]

private theorem w10 : noncentralWhitneySecond m a 1 0 = -a := by
  simp [noncentralWhitneySecond]

private theorem w11 : noncentralWhitneySecond m a 1 1 = 1 := by
  simp [noncentralWhitneySecond]

private theorem w20 : noncentralWhitneySecond m a 2 0 = a ^ 2 := by
  simp [noncentralWhitneySecond]

private theorem w21 : noncentralWhitneySecond m a 2 1 = -a + (m - a) := by
  simp [noncentralWhitneySecond]

private theorem w22 : noncentralWhitneySecond m a 2 2 = 1 := by
  simp [noncentralWhitneySecond]

private theorem w23 : noncentralWhitneySecond m a 2 3 = 0 := by
  simp [noncentralWhitneySecond]

private theorem p0 : noncentralTannyDowlingPolynomial m a 0 = 1 := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond]

private theorem p1 :
    noncentralTannyDowlingPolynomial m a 1 = Polynomial.C (-a) + Polynomial.X := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond, Finset.sum_range_succ]

private theorem p2 :
    noncentralTannyDowlingPolynomial m a 2 =
      Polynomial.C (a ^ 2) + Polynomial.C (-a + (m - a)) * Polynomial.X +
        2 * Polynomial.X ^ 2 := by
  simp [noncentralTannyDowlingPolynomial, noncentralWhitneySecond, Finset.sum_range_succ]
