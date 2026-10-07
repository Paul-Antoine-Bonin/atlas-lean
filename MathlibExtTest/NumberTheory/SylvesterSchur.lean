/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SylvesterSchur

example {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k :=
  Nat.exists_prime_gt_and_dvd_ascFactorial hk hkn
