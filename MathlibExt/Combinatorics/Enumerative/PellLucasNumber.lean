/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Pell--Lucas numbers

Source: K. Kaygisiz and A. Şahin, *Generalized Bivariate Lucas p-Polynomials and Hessenberg
Matrices*, Journal of Integer Sequences 15 (2012),
[`kaygisiz3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL15/Kaygisiz/kaygisiz3.tex).
-/

/-- The Pell--Lucas sequence, initialized by `Q₀ = Q₁ = 2` and satisfying
`Qₙ₊₂ = 2 Qₙ₊₁ + Qₙ`. This is the source's specialization
`L_{1,n}(2,1)`. -/
public def pellLucas : Nat → Nat
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * pellLucas (n + 1) + pellLucas n

public theorem pellLucas_zero : pellLucas 0 = 2 := rfl

public theorem pellLucas_one : pellLucas 1 = 2 := rfl

public theorem pellLucas_add_two (n : Nat) :
    pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n := rfl

end

end MetaMathlibExt
