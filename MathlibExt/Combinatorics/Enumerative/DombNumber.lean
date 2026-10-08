/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ZagierNumber

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-!
# Domb numbers

Source: G.-R. Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024),
[`zhang9.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex).

Remark Rem1.8 introduces the sequence of *Domb numbers* (OEIS A002895) as
`(Domb(n))_{n=0}^∞ := (D(n,2,1,1))_{n=0}^∞`, where `D(n,r,s,t)` is the Domb-type sum
`D(n,r,s,t) = ∑_{k=0}^n choose(n,k)^r choose(2k,k)^s choose(2(n-k),n-k)^t`.
We formalize it as the specialization `D(n,2,1,1)` of `MetaMathlibExt.dombTypeSum`.
-/

/-- The Domb numbers `Domb(n) = D(n,2,1,1)` (OEIS A002895). -/
public def dombNumber (n : ℕ) : ℕ :=
  dombTypeSum n 2 1 1

/-- Unfolded sum for the Domb numbers, with the powers of one simplified. -/
public theorem dombNumber_unfold (n : ℕ) :
    dombNumber n =
      ∑ k ∈ Finset.range (n + 1),
        n.choose k ^ 2 * (2 * k).choose k * (2 * (n - k)).choose (n - k) := by
  unfold dombNumber dombTypeSum
  simp only [pow_one]

end

end MetaMathlibExt
