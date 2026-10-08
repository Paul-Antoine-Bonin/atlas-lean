/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares
public import Mathlib.Data.Rat.Defs
import Batteries.Util.ProofWanted

@[expose] public section

namespace Nat

/-- Hurwitz class number `H`. Source: arXiv:2307.05244 `main.tex` lines 359-365
    (span SHA-256 `b04cba9e14e90ed1b64100eda01d08dd3de6e1d2b2ea9ec9b1a56cfc467f6622`):
    `H(N) = 0` if `N ≡ 1` or `2 mod 4`; `H(0) = -1 / 12`; otherwise `N > 0`
    and `N ≡ 0` or `3 mod 4`, `H(N)` is the class number of not necessarily
    primitive positive-definite quadratic forms of discriminant `-N`, with
    weight `1 / 2` for forms equivalent to `a * (x ^ 2 + y ^ 2)` and weight
    `1 / 3` for forms equivalent to `a * (x ^ 2 + x * y + y ^ 2)`. -/
def_wanted hurwitzClassNumber : ℕ → ℚ

/-- Gauss formula, residues 1,2,5,6 mod 8: `r₃(n) = 12 * H(4 * n)`.
    Source: arXiv:2307.05244 `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem_wanted threeSquareRepresentationCount_eq_twelve_mul_hurwitzClassNumber_four_n
    (n : ℕ) (hn : 0 < n)
    (h : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 5 ∨ n % 8 = 6) :
    (threeSquareRepresentationCount n : ℚ) = 12 * ❰hurwitzClassNumber❱ (4 * n)

/-- Gauss formula, residue 3 mod 8: `r₃(n) = 24 * H(n)`. Source:
    arXiv:2307.05244 `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem_wanted threeSquareRepresentationCount_eq_twenty_four_mul_hurwitzClassNumber
    (n : ℕ) (hn : 0 < n) (h : n % 8 = 3) :
    (threeSquareRepresentationCount n : ℚ) = 24 * ❰hurwitzClassNumber❱ n

end Nat
