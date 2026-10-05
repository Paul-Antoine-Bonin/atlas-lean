module

import MathlibExt.NumberTheory.Padics.Polynomial

open Polynomial

private theorem prime_two : Nat.Prime 2 := by decide

private theorem twelve_ne_zero : (12 : ℤ) ≠ 0 := by decide

private theorem padicValInt_two_twelve : padicValInt 2 (12 : ℤ) = 2 := by
  let _ := Fact.mk prime_two
  have h2 : 2 ≤ padicValInt 2 (12 : ℤ) := by
    rcases (padicValInt_dvd_iff (p := 2) 2 12).mp (by norm_num) with h | h
    · norm_num at h
    · exact h
  have h3 : ¬3 ≤ padicValInt 2 (12 : ℤ) := by
    intro h
    have hd : (2 : ℤ) ^ 3 ∣ 12 := (padicValInt_dvd_iff (p := 2) 3 12).mpr (Or.inr h)
    norm_num at hd
  omega

example :
    Polynomial.padicValuation 2 prime_two (C 12)
      (C_ne_zero.mpr twelve_ne_zero) = 2 := by
  calc
    Polynomial.padicValuation 2 prime_two (C 12) (C_ne_zero.mpr twelve_ne_zero) =
        padicValInt 2 12 := Polynomial.padicValuation_C 2 prime_two 12 twelve_ne_zero
    _ = 2 := padicValInt_two_twelve

example (f : Polynomial ℤ) (hf : f ≠ 0) (n : ℕ) (hn : n ∈ f.support) :
    Polynomial.padicValuation 2 prime_two f hf ≤ padicValInt 2 (f.coeff n) :=
  Polynomial.padicValuation_le_coeff hn

example (f : Polynomial ℤ) (hf : f ≠ 0) (k : ℕ)
    (hk : ∀ n ∈ f.support, k ≤ padicValInt 2 (f.coeff n)) :
    k ≤ Polynomial.padicValuation 2 prime_two f hf :=
  Polynomial.le_padicValuation hk
