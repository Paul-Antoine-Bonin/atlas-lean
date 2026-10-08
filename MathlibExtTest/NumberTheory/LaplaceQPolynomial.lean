/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaplaceQPolynomial

namespace MetaMathlibExt

/-- Auxiliary iteration carrying the pair `(Q n, Q (n + 1))` for the positive
witness. Base `(1, X)`; step `(a, b) ↦ (b, X * b + (n + 2) • a)`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private noncomputable def Qpair : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1, Polynomial.X)
  | Nat.succ n => ((Qpair n).2, Polynomial.X * (Qpair n).2 + (n + 2) • (Qpair n).1)

/-- Positive-witness Q-family: first projection of `Qpair`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private noncomputable def Qwit : ℕ → Polynomial ℤ := fun n => (Qpair n).1

/-- Positive-witness P-family: `P 0 = 0` and
`P (n + 1) = Q (n + 1) - derivative (Q n)`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private noncomputable def Pwit : ℕ → Polynomial ℤ
  | 0 => 0
  | Nat.succ n => Qwit (Nat.succ n) - Polynomial.derivative (Qwit n)

/-- The positive witness satisfies the three-term recurrence at every rank.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private theorem Qwit_two_step_add (n : ℕ) :
    Qwit (n + 2) = Polynomial.X * Qwit (n + 1) + (n + 2) • Qwit n :=
  rfl

/-- The positive witness satisfies the derivative recurrence at every rank.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private theorem Qwit_first_eq_add (n : ℕ) :
    Qwit (n + 1) = Pwit (n + 1) + Polynomial.derivative (Qwit n) := by
  have hP : Pwit (n + 1) = Qwit (n + 1) - Polynomial.derivative (Qwit n) := rfl
  rw [hP]
  exact (sub_add_cancel _ _).symm

/-- Positive witness: the pair `(Pwit, Qwit)` satisfies both Q recurrences.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private theorem positive_witness_is_family :
    IsLaplaceQFamily Pwit Qwit := by
  unfold IsLaplaceQFamily
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk_eq : k = (k - 1) + 1 := by omega
  have hsub : (k - 1) + 1 - 1 = k - 1 := by omega
  have hadd : (k - 1) + 1 + 1 = (k - 1) + 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [hk_eq, hsub]
    exact Qwit_first_eq_add (k - 1)
  · rw [hk_eq, hsub, hadd]
    exact Qwit_two_step_add (k - 1)

/-- Constant-zero P-family for the negative witness.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private noncomputable def Pneg : ℕ → Polynomial ℤ := fun _ => 0

/-- Constant-one Q-family for the negative witness.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private noncomputable def Qneg : ℕ → Polynomial ℤ := fun _ => 1

/-- Negative witness: the constant families violate the derivative recurrence
at `k = 1`, hence fail the predicate.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private theorem negative_witness_fails : ¬ IsLaplaceQFamily Pneg Qneg := by
  unfold IsLaplaceQFamily
  rintro ⟨_, hrec⟩
  have h1 := (hrec 1 le_rfl).1
  have e1 : Qneg 1 = (1 : Polynomial ℤ) := rfl
  have e2 : Pneg 1 = (0 : Polynomial ℤ) := rfl
  have e3 : Qneg (1 - 1) = (1 : Polynomial ℤ) := rfl
  rw [e1, e2, e3, Polynomial.derivative_one] at h1
  simp at h1

end MetaMathlibExt
