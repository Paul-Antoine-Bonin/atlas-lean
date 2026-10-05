module

import MathlibExt.NumberTheory.Padics.Digits

set_option autoImplicit false

open PadicInt Finset

namespace PadicIntTest

variable {p : Nat} [Fact p.Prime]

/-- Digit bound check. -/
example (a : ℤ_[p]) (n : Nat) : padicDigit a n < p :=
  padicDigit_lt a n

/-- Bundled expansion stays inside `Fin p`. -/
example (a : ℤ_[p]) (n : Nat) : (padicExpansion a n).val < p :=
  (padicExpansion a n).isLt

/-- Value bridge check. -/
example (a : ℤ_[p]) (n : Nat) : (padicExpansion a n).val = padicDigit a n :=
  padicExpansion_val a n

/-- One-step reconstruction check. -/
example (a : ℤ_[p]) (n : Nat) :
    padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n :=
  padicDigit_mul_pow a n

/-- Successor approximation check, including the `.val` form. -/
example (a : ℤ_[p]) (n : Nat) :
    a.appr (n + 1) = a.appr n + (padicExpansion a n).val * p ^ n :=
  appr_succ_eq_val a n

/-- Finite-sum reconstruction check. -/
example (a : ℤ_[p]) (n : Nat) :
    a.appr n = ∑ k ∈ Finset.range n, (padicExpansion a k).val * p ^ k :=
  appr_eq_sum_expansion_val a n

/-- Every approximation of the zero `p`-adic integer is zero. -/
theorem appr_zero_test (n : Nat) : PadicInt.appr (0 : ℤ_[p]) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [PadicInt.appr, ih]

/-- Zero `p`-adic integer has zero digits. -/
example (n : Nat) : padicDigit (0 : ℤ_[p]) n = 0 := by
  simp [padicDigit, appr_zero_test]

/-- Zero `p`-adic integer has zero bundled expansion. -/
example (n : Nat) : (padicExpansion (0 : ℤ_[p]) n).val = 0 := by
  simp [padicExpansion_val, padicDigit, appr_zero_test]

end PadicIntTest
