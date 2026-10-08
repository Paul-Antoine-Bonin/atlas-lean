/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSpecialPrime
public import Mathlib.Tactic

namespace MetaMathlibExt

example : IsLucasSpecialPrime 12 18 2 := by norm_num [IsLucasSpecialPrime, Int.gcd]

example : IsLucasSpecialPrime 12 18 3 := by norm_num [IsLucasSpecialPrime, Int.gcd]

example : ¬ IsLucasSpecialPrime 12 18 5 := by norm_num [IsLucasSpecialPrime, Int.gcd]

example : ¬ IsLucasSpecialPrime 12 18 1 := by norm_num [IsLucasSpecialPrime, Int.gcd]

example : IsLucasSpecialPrime (-12) 18 2 := by norm_num [IsLucasSpecialPrime, Int.gcd]

example {P Q : Int} {p : Nat} (h : IsLucasSpecialPrime P Q p) :
    Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q :=
  (isLucasSpecialPrime_iff P Q p).mp h

example {P Q : Int} {p : Nat}
    (h : Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q) :
    IsLucasSpecialPrime P Q p :=
  (isLucasSpecialPrime_iff P Q p).mpr h

end MetaMathlibExt
