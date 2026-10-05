module

public import MathlibExt.Algebra.Polynomial.UnsignedCharlierPolynomialsOfOrder0

namespace MetaMathlibExt

@[expose] public section

theorem unsignedCharlierOrder0_nat_zero :
    unsignedCharlierOrder0 ℕ 0 = 1 := by
  simp [unsignedCharlierOrder0, ascPochhammer_zero]
  try ring

theorem unsignedCharlierOrder0_nat_one :
    unsignedCharlierOrder0 ℕ 1 = 1 + Polynomial.X := by
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

theorem unsignedCharlierOrder0_nat_two :
    unsignedCharlierOrder0 ℕ 2 = 1 + 3 * Polynomial.X + Polynomial.X ^ 2 := by
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

theorem unsignedCharlierOrder0_nat_three :
    unsignedCharlierOrder0 ℕ 3 =
      1 + 8 * Polynomial.X + 6 * Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

end

end MetaMathlibExt
