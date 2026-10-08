/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PQPatalanNumbers

/-!
# (p,q)-super Patalan numbers

This file formalizes a definition from Thomas M. Richardson, *The Super
Patalan Numbers*, Journal of Integer Sequences 18 (2015), Article 15.3.3.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- The `(p,q)`-super Patalan number
`Q(i,j) = (-1)^j p^(2(i+j)) binom(i-q/p, i+j)`.

The bundled parameter records `p > 1` and `0 < q < p`. Stable source
identifier: concept `jis_sem_6d22b6520f5edbfe81e62b58`, statement
`jis_a9d7ecad34cde5accbc27d08`.
-/
def pqSuperPatalanNumber (P : PQPatalanParams) (i j : ℕ) : ℚ :=
  (-1) ^ j * (P.p : ℚ) ^ (2 * (i + j)) *
    patalanGeneralizedBinomial ((i : ℚ) - (P.q : ℚ) / P.p) (i + j)

/-- Super Patalan numbers of order `p`, obtained by specializing `q` to `1`. -/
def superPatalanNumber (p i j : ℕ) (hp : 1 < p) : ℚ :=
  pqSuperPatalanNumber
    { p := p, q := 1, hp := hp, hq_pos := by omega, hq := hp } i j

end

end MetaMathlibExt
