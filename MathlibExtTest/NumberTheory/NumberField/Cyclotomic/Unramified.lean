/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Cyclotomic.Unramified
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped NumberField

namespace MathlibExtTest.NumberTheory.CyclotomicUnramified

-- `Q(zeta_5)` is unramified at `2`, since `2` does not divide `5`.
example : Algebra.IsUnramifiedIn
    (𝓞 (CyclotomicField 5 ℚ)) (Ideal.span {(2 : ℤ)}) := by
  let _ : NeZero 5 := ⟨by decide⟩
  let _ : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  let _ : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact IsCyclotomicExtension.Rat.isUnramifiedIn_of_not_dvd (m := 5) (p := 2)
    Nat.prime_two (CyclotomicField 5 ℚ) (by norm_num)

-- The `2`-free conductor of `12` gives an unramified cyclotomic field at `2`.
example : Algebra.IsUnramifiedIn
    (𝓞 (CyclotomicField (Nat.divMaxPow 12 2) ℚ))
    (Ideal.span {(2 : ℤ)}) := by
  let _ : NeZero 12 := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.isUnramifiedIn_divMaxPow
    12 2 Nat.prime_two

-- Pointwise ramification index extracted from the native statement.
example {m p : ℕ} [NeZero m] (hp : p.Prime) (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (hm : ¬ p ∣ m) (P : Ideal (𝓞 K)) [P.IsPrime]
    (hLie : P.LiesOver (Ideal.span {(p : ℤ)})) :
    Ideal.ramificationIdx P ℤ = 1 :=
  Algebra.IsUnramifiedIn.ramificationIdx_eq_one
    (IsCyclotomicExtension.Rat.isUnramifiedIn_of_not_dvd hp K hm) hLie

-- A subfield of a `p`-power cyclotomic extension unramified at `p` is `⊥`.
example {p e : ℕ} (hp : p.Prime) (L : Type*) [Field L] [NumberField L]
    (E₁ : IntermediateField ℚ L) [IsCyclotomicExtension {p ^ e} ℚ E₁]
    (F : IntermediateField ℚ L) (hFE₁ : F ≤ E₁)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)})) :
    F = ⊥ :=
  IsCyclotomicExtension.Rat.eq_bot_of_isUnramifiedIn_prime_pow (e := e) hp L E₁
    F hFE₁ hF

-- Source-shaped specialization with exponent `padicValNat p m`.
example {m p : ℕ} [NeZero m] (hp : p.Prime) (L : Type*) [Field L]
    [NumberField L]
    (E₁ : IntermediateField ℚ L)
    [IsCyclotomicExtension {p ^ padicValNat p m} ℚ E₁]
    (F : IntermediateField ℚ L) (hFE₁ : F ≤ E₁)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)})) :
    F = ⊥ :=
  IsCyclotomicExtension.Rat.eq_bot_of_isUnramifiedIn_prime_pow
    (e := padicValNat p m) hp L E₁ F hFE₁ hF

end MathlibExtTest.NumberTheory.CyclotomicUnramified
