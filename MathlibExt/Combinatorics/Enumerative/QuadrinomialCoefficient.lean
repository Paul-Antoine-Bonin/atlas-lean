/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# Quadrinomial coefficients

The `m = 4` instance of the polynomial coefficients (OEIS A008287).

Source: E. Munarini, *Shifting Properties of Riordan, Sheffer and Connection Constants*:
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Munarini/muna4.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Quadrinomial coefficient `{n; 4 choose k}` (concept `jis_sem_21c48e3801524f9403d681b0`,
source statement `jis_cb7e03aa435f1bbd253660ca`, OEIS A008287): the coefficient
of `x ^ k` in `(1 + x + x ^ 2 + x ^ 3) ^ n`, with `0 ≤ k ≤ 3 * n`. -/
noncomputable def polynomialQuadrinomialCoeff (n k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℕ) ^ n).coeff k

end

end MetaMathlibExt
