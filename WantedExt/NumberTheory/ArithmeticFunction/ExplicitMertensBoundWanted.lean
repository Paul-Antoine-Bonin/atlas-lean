/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

namespace MetaMathlibExt

/--
Explicit Mertens-type bounds for the summatory Möbius-over-`n` function:
`|∑_{n ≤ x} μ(n)/n| < 0.19/log x` for `x ≥ 33` and `< 546/(log x)^2`
for `x > 1`.

Source: Olivier Bordellès,
"Some Explicit Estimates for the Möbius Function,"
Journal of Integer Sequences 18 (2015), Article 15.11.1,
Theorem (label t1), items (a) and (b), lines 118–127,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Bordelles2/bordelles21.tex

The sum ranges over `Finset.Icc 1 ⌊x⌋₊`, i.e. `n ≤ x`. These bounds
improve the author's equation (e4) (`0.2185/log x` and `726/(log x)^2`).
Spot-checked against exact partial sums at `N = 33, 40, 50, 100, 200, 500`,
all satisfying both bounds (tightest at `N = 40`: `0.0505 < 0.0515`).
-/
public theorem_wanted summatory_moebius_div_bound :
    (∀ x : ℝ, 33 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| <
        (0.19 : ℝ) / Real.log x) ∧
    (∀ x : ℝ, 1 < x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| <
        546 / (Real.log x) ^ 2)

end MetaMathlibExt
