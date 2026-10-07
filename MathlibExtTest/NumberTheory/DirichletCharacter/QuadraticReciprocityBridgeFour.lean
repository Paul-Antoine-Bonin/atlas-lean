/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeFour
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
Probes for the even-family reductions
(`chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four`,
`jacobiSym_four_mul_of_odd`, `jacobiSym_two_mul_of_odd`), the odd-denominator
multiplicativity (`kroneckerSym_mul_of_odd`), the Kronecker-Jacobi identity
(`kroneckerSym_eq_jacobiSym_of_odd`), and the odd-`p` mod-3 bridge
(`chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four`).

Covered: the `4 * m` bridge at odd `p` with `m % 4 = 3` for both signs of
`m`, at prime denominators `(3, 7)`, `(-5, 7)`, `(7, 5)` and composite
denominators `(3, 9)`, `(7, 9)`, `(-5, 9)`, `(7, 15)`, plus the two one-step
reductions, which hold for `m` of any residue and either sign.

Value pins (each side computed independently to a literal, without invoking
the theorem under test):
* `(m, p) = (3, 7)`: `jacobiSym` is `1`, `kroneckerSym` is `-1`, and
  `(ZMod.χ₄ 7 : ℤ)` is `-1`, so the corrected agreement is `(-1) * 1 = -1`.
* `(m, p) = (-5, 7)`: `jacobiSym` is `-1`, `kroneckerSym` is `1`, and
  `(ZMod.χ₄ 7 : ℤ)` is `-1`, so the corrected agreement is `(-1) * -1 = 1`.
* `(m, p) = (7, 5)`: `jacobiSym` is `-1`, `kroneckerSym` is `-1`, and
  `(ZMod.χ₄ 5 : ℤ)` is `1`, so the correction is trivial yet the
  reciprocity path is still exercised.
* `(m, p) = (5, 3)`: outside the covered branch (`(5 : ℤ) % 4 = 1`),
  pinning the `h3` hypothesis as a truth condition. Here `jacobiSym` is
  `-1`, `kroneckerSym (4 * m)` is `-1`, and `(ZMod.χ₄ 3 : ℤ)` is `-1`, so
  the corrected left side is `(-1) * (-1) = 1` and disagrees with `-1`.

Composite rows (the point of the weakening to odd `p`): at `p = 9` each row
independently pins all three literals, `χ₄`, Jacobi (via `norm_num`), and
Kronecker, then checks agreement and instantiates the bridge:
* `(3, 9)`: `kroneckerSym` is `0`, `jacobiSym` is `0`, `(ZMod.χ₄ 9 : ℤ)` is `1`.
* `(7, 9)`: `kroneckerSym` is `1`, `jacobiSym` is `1`, `(ZMod.χ₄ 9 : ℤ)` is `1`.
* `(-5, 9)`: `kroneckerSym` is `1`, `jacobiSym` is `1`, `(ZMod.χ₄ 9 : ℤ)` is `1`.
The `Kronecker` literals do NOT go through the new
`kroneckerSym_eq_jacobiSym_of_odd`: the definitional route
(`kroneckerSym D 9` unfolds to `kroneckerAtPrime D 3` squared since
`Nat.primeFactorsList 9 = [3, 3]`) is blocked because that list identity
resisted `decide`, `norm_num`, and `rfl` (`decide` does not reduce
`Nat.primeFactorsList`). They go through the landed `kroneckerSym_mul`
plus the landed `kroneckerSym_prime`/`kroneckerAtPrime`/`legendreSym` route
at `3`; both landed results predate this diff, hence are independent of
everything under test.

Composite disagreement row (the gap that matters): `(7, 15)` is the first
composite row with `χ₄ p ≠ 1` (`15 % 4 = 3`, `15` composite).
`kroneckerSym` is `-1`, `jacobiSym` is `1`, `(ZMod.χ₄ 15 : ℤ)` is `-1`, so
the corrected agreement is `(-1) * 1 = -1` while the uncorrected side is
`1` and disagrees with `-1`. Both the agreement probe and an `uncorrected
fails` probe are present, mirroring `uncorrMain3_7`. The Kronecker pin
splits `15 = 3 * 5` via the landed `kroneckerSym_mul`, reusing
`kronBase28_3` (`1`) and `kronMain7_5` (`-1`).

Multiplicativity probe (`kroneckerSym_mul_of_odd`) at `D = 7`,
`15 = 3 * 5`: `kroneckerSym 7 3` is `1`, `kroneckerSym 7 5` is `-1`, and
the composite `kroneckerSym 7 15` is `-1`, each pinned via the landed
`kroneckerSym_mul` plus the prime route (never through the theorem under
test), with a value agreement probe and an instantiation at `(7, 3, 5)`.

`kroneckerSym_eq_jacobiSym_of_odd` at `D = -1`, `p = 9` (the case the whole
diff turns on): the Jacobi side is pinned to `1`; the Kronecker side
`kroneckerSym (-1) 9` is NOT independently pinned, since the landed
`kroneckerSym_mul` needs `D ≠ -1` and the definitional `primeFactorsList`
route stays blocked, and routing through the theorem under test would be
circular. The row instantiates the theorem with only the Jacobi literal
pinned.

Odd-`p` mod-3 bridge
(`chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four`) at
composite `p`: `(7, 15)` pins all three literals (`kroneckerSym` `-1`,
`χ₄` `-1`, `jacobiSym` `1`) with agreement `(-1) * 1 = -1` and instantiates
the bridge; `(-1, 9)` pins `χ₄` (`1`) and Jacobi (`1`, denominator
`(-1).natAbs = 1`) and instantiates the bridge, sharing the unpinned
`kroneckerSym (-1) 9` above (`(-1 : ℤ) % 4 = 3` holds).

Reduction pins (again each side to a literal):
* `(m, p) = (3, 7)`: `jac (4 * m)`, `jac m`, `jac (2 * m)` are `-1`, `-1`,
  `-1`, and `(ZMod.χ₈ 7 : ℤ)` is `1`.
* `(m, p) = (5, 3)`: `-1`, `-1`, `1`, and `(ZMod.χ₈ 3 : ℤ)` is `-1`.
* `(m, p) = (-3, 5)`: `-1`, `-1`, `1`, and `(ZMod.χ₈ 5 : ℤ)` is `-1`.

The `(3, 7)` pair carries the point of the main theorem: the Jacobi side
is `1` while the Kronecker side is `-1`, so the uncorrected identity fails
there and the `χ₄ p` factor is not decoration.

Bridge instantiations apply the `4 * m` theorem at `(3, 7)`, `(-5, 7)`,
`(7, 5)`, `(3, 9)`, `(7, 9)`, `(-5, 9)`, and `(7, 15)`; the multiplicativity
theorem at `(7, 3, 5)`; the Kronecker-Jacobi identity at `(-1, 9)`; the
odd-`p` mod-3 bridge at `(7, 15)` and `(-1, 9)`; and each reduction at
`(3, 7)`, `(5, 3)`, and `(-3, 5)`. The `(5, 3)` main-branch probe has no
bridge instantiation since `(5 : ℤ) % 4 = 1` does not satisfy `h3`.

Scope pins: `(3 : ℤ) % 4 = 3`, `(-5 : ℤ) % 4 = 3`, `(7 : ℤ) % 4 = 3`,
`(-1 : ℤ) % 4 = 3`, `(5 : ℤ) % 4 = 1`, `Odd 7`, `Odd 9`, `Odd 15`.
Reduction notes: `decide` closes the `%`-facts, the `p ≠ 2` side
conditions, the `Odd` facts, and small closed numeric goals; `jacobiSym`
at concrete arguments needs `norm_num` with the `LegendreSymbol`
extension; `Nat.Prime` needs the `Prime` extension. `kroneckerSym` at prime
denominators goes through `kroneckerSym_prime`, `kroneckerAtPrime`, the
`legendreSym`-to-`jacobiSym` lemma, then `norm_num`; at composite
denominators with `D ≠ -1` through landed `kroneckerSym_mul` plus that
prime route. `ZMod.χ₄` at a literal reduces via
`ZMod.χ₄_nat_three_mod_four` or `ZMod.χ₄_nat_one_mod_four` with a `decide`
side condition. `ZMod.χ₈` at a literal is pinned via `jacobiSym.at_two`
plus `norm_num` on `jacobiSym 2 p`. The `agree` probes rewrite with the
pins (`rw`, not `simp`) and close the bare arithmetic goal with `decide`.
-/

open MetaMathlibExt

private theorem chi7 : (ZMod.χ₄ 7 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

private theorem chi5 : (ZMod.χ₄ 5 : ℤ) = 1 :=
  ZMod.χ₄_nat_one_mod_four (by decide)

private theorem chi3 : (ZMod.χ₄ 3 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

private theorem chi9 : (ZMod.χ₄ 9 : ℤ) = 1 :=
  ZMod.χ₄_nat_one_mod_four (by decide)

private theorem jacMain3_7 : jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs = 1 := by norm_num

private theorem kronMain3_7 : kroneckerSym (4 * (3 : ℤ)) 7 = -1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hp2 : 7 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 7) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (3 : ℤ)) 7 = kroneckerAtPrime (4 * (3 : ℤ)) 7 :=
    kroneckerSym_prime (4 * (3 : ℤ)) 7 hp
  have hat : kroneckerAtPrime (4 * (3 : ℤ)) 7 = legendreSym 7 (4 * (3 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 7 (4 * (3 : ℤ)) = jacobiSym (4 * (3 : ℤ)) 7 :=
    jacobiSym.legendreSym.to_jacobiSym 7 (4 * (3 : ℤ))
  have hjac : jacobiSym (4 * (3 : ℤ)) 7 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem agreeMain3_7 :
    (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs =
      kroneckerSym (4 * (3 : ℤ)) 7 := by
  rw [chi7, jacMain3_7, kronMain3_7]
  decide

private theorem uncorrMain3_7 :
    jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs ≠ kroneckerSym (4 * (3 : ℤ)) 7 := by
  rw [jacMain3_7, kronMain3_7]
  decide

private theorem bridgeMain3_7 :
    (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (3 : ℤ).natAbs =
      kroneckerSym (4 * (3 : ℤ)) 7 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    3 7 (by decide) (by decide)

private theorem jacMainNeg5_7 : jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs = -1 := by norm_num

private theorem kronMainNeg5_7 : kroneckerSym (4 * (-5 : ℤ)) 7 = 1 := by
  have hp : Nat.Prime 7 := by norm_num
  have hp2 : 7 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 7) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (-5 : ℤ)) 7 = kroneckerAtPrime (4 * (-5 : ℤ)) 7 :=
    kroneckerSym_prime (4 * (-5 : ℤ)) 7 hp
  have hat : kroneckerAtPrime (4 * (-5 : ℤ)) 7 = legendreSym 7 (4 * (-5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 7 (4 * (-5 : ℤ)) = jacobiSym (4 * (-5 : ℤ)) 7 :=
    jacobiSym.legendreSym.to_jacobiSym 7 (4 * (-5 : ℤ))
  have hjac : jacobiSym (4 * (-5 : ℤ)) 7 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem agreeMainNeg5_7 :
    (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs =
      kroneckerSym (4 * (-5 : ℤ)) 7 := by
  rw [chi7, jacMainNeg5_7, kronMainNeg5_7]
  decide

private theorem uncorrMainNeg5_7 :
    jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs ≠ kroneckerSym (4 * (-5 : ℤ)) 7 := by
  rw [jacMainNeg5_7, kronMainNeg5_7]
  decide

private theorem bridgeMainNeg5_7 :
    (ZMod.χ₄ 7 : ℤ) * jacobiSym ((7 : ℕ) : ℤ) (-5 : ℤ).natAbs =
      kroneckerSym (4 * (-5 : ℤ)) 7 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    (-5) 7 (by decide) (by decide)

private theorem jacMain7_5 : jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs = -1 := by norm_num

private theorem kronMain7_5 : kroneckerSym (4 * (7 : ℤ)) 5 = -1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : 5 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 5) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (7 : ℤ)) 5 = kroneckerAtPrime (4 * (7 : ℤ)) 5 :=
    kroneckerSym_prime (4 * (7 : ℤ)) 5 hp
  have hat : kroneckerAtPrime (4 * (7 : ℤ)) 5 = legendreSym 5 (4 * (7 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 5 (4 * (7 : ℤ)) = jacobiSym (4 * (7 : ℤ)) 5 :=
    jacobiSym.legendreSym.to_jacobiSym 5 (4 * (7 : ℤ))
  have hjac : jacobiSym (4 * (7 : ℤ)) 5 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem agreeMain7_5 :
    (ZMod.χ₄ 5 : ℤ) * jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 5 := by
  rw [chi5, jacMain7_5, kronMain7_5]
  decide

private theorem bridgeMain7_5 :
    (ZMod.χ₄ 5 : ℤ) * jacobiSym ((5 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 5 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 5 (by decide) (by decide)

private theorem jacOut5_3 : jacobiSym ((3 : ℕ) : ℤ) (5 : ℤ).natAbs = -1 := by norm_num

private theorem kronOut5_3 : kroneckerSym (4 * (5 : ℤ)) 3 = -1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (5 : ℤ)) 3 = kroneckerAtPrime (4 * (5 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (5 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (5 : ℤ)) 3 = legendreSym 3 (4 * (5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (5 : ℤ)) = jacobiSym (4 * (5 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (5 : ℤ))
  have hjac : jacobiSym (4 * (5 : ℤ)) 3 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem disagreeOut5_3 :
    (ZMod.χ₄ 3 : ℤ) * jacobiSym ((3 : ℕ) : ℤ) (5 : ℤ).natAbs ≠
      kroneckerSym (4 * (5 : ℤ)) 3 := by
  rw [chi3, jacOut5_3, kronOut5_3]
  decide

private theorem kronBase12_3 : kroneckerSym (4 * (3 : ℤ)) 3 = 0 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (3 : ℤ)) 3 = kroneckerAtPrime (4 * (3 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (3 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (3 : ℤ)) 3 = legendreSym 3 (4 * (3 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (3 : ℤ)) = jacobiSym (4 * (3 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (3 : ℤ))
  have hjac : jacobiSym (4 * (3 : ℤ)) 3 = 0 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem kronComp3_9 : kroneckerSym (4 * (3 : ℤ)) 9 = 0 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (3 : ℤ)) (3 * 3) =
      kroneckerSym (4 * (3 : ℤ)) 3 * kroneckerSym (4 * (3 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (3 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBase12_3]
  decide

private theorem jacComp3_9 : jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs = 0 := by norm_num

private theorem agreeComp3_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs =
      kroneckerSym (4 * (3 : ℤ)) 9 := by
  rw [chi9, jacComp3_9, kronComp3_9]
  decide

private theorem bridgeComp3_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (3 : ℤ).natAbs =
      kroneckerSym (4 * (3 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    3 9 (by decide) (by decide)

private theorem kronBase28_3 : kroneckerSym (4 * (7 : ℤ)) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (7 : ℤ)) 3 = kroneckerAtPrime (4 * (7 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (7 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (7 : ℤ)) 3 = legendreSym 3 (4 * (7 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (7 : ℤ)) = jacobiSym (4 * (7 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (7 : ℤ))
  have hjac : jacobiSym (4 * (7 : ℤ)) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem kronComp7_9 : kroneckerSym (4 * (7 : ℤ)) 9 = 1 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (7 : ℤ)) (3 * 3) =
      kroneckerSym (4 * (7 : ℤ)) 3 * kroneckerSym (4 * (7 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (7 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBase28_3]
  decide

private theorem jacComp7_9 : jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs = 1 := by norm_num

private theorem agreeComp7_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 9 := by
  rw [chi9, jacComp7_9, kronComp7_9]
  decide

private theorem bridgeComp7_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 9 (by decide) (by decide)

private theorem kronBaseNeg20_3 : kroneckerSym (4 * (-5 : ℤ)) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (4 * (-5 : ℤ)) 3 = kroneckerAtPrime (4 * (-5 : ℤ)) 3 :=
    kroneckerSym_prime (4 * (-5 : ℤ)) 3 hp
  have hat : kroneckerAtPrime (4 * (-5 : ℤ)) 3 = legendreSym 3 (4 * (-5 : ℤ)) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (4 * (-5 : ℤ)) = jacobiSym (4 * (-5 : ℤ)) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (4 * (-5 : ℤ))
  have hjac : jacobiSym (4 * (-5 : ℤ)) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem kronCompNeg5_9 : kroneckerSym (4 * (-5 : ℤ)) 9 = 1 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  have hmul : kroneckerSym (4 * (-5 : ℤ)) (3 * 3) =
      kroneckerSym (4 * (-5 : ℤ)) 3 * kroneckerSym (4 * (-5 : ℤ)) 3 :=
    kroneckerSym_mul (4 * (-5 : ℤ)) (by decide) 3 3
  rw [h9, hmul, kronBaseNeg20_3]
  decide

private theorem jacCompNeg5_9 : jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs = 1 := by norm_num

private theorem agreeCompNeg5_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs =
      kroneckerSym (4 * (-5 : ℤ)) 9 := by
  rw [chi9, jacCompNeg5_9, kronCompNeg5_9]
  decide

private theorem bridgeCompNeg5_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-5 : ℤ).natAbs =
      kroneckerSym (4 * (-5 : ℤ)) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    (-5) 9 (by decide) (by decide)

private theorem chi15 : (ZMod.χ₄ 15 : ℤ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

private theorem jacComp7_15 : jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs = 1 := by norm_num

private theorem kronComp28_15 : kroneckerSym (4 * (7 : ℤ)) 15 = -1 := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  have hmul : kroneckerSym (4 * (7 : ℤ)) (3 * 5) =
      kroneckerSym (4 * (7 : ℤ)) 3 * kroneckerSym (4 * (7 : ℤ)) 5 :=
    kroneckerSym_mul (4 * (7 : ℤ)) (by decide) 3 5
  rw [h15, hmul, kronBase28_3, kronMain7_5]
  decide

private theorem agreeComp7_15 :
    (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 15 := by
  rw [chi15, jacComp7_15, kronComp28_15]
  decide

private theorem uncorrComp7_15 :
    jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs ≠ kroneckerSym (4 * (7 : ℤ)) 15 := by
  rw [jacComp7_15, kronComp28_15]
  decide

private theorem bridgeComp7_15 :
    (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (4 * (7 : ℤ)) 15 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_four_mul_three_mod_four
    7 15 (by decide) (by decide)

private theorem jac4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = -1 := by norm_num

private theorem jacm_3_7 : jacobiSym (3 : ℤ) 7 = -1 := by norm_num

private theorem jac2_3_7 : jacobiSym (2 * (3 : ℤ)) 7 = -1 := by norm_num

private theorem chi8_7 : (ZMod.χ₈ 7 : ℤ) = 1 := by
  have hat : jacobiSym (2 : ℤ) 7 = (ZMod.χ₈ 7 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 7 = 1 := by norm_num
  rw [← hat]
  exact hjac

private theorem agreeRed4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = jacobiSym (3 : ℤ) 7 := by
  rw [jac4_3_7, jacm_3_7]

private theorem agreeRed2_3_7 :
    jacobiSym (2 * (3 : ℤ)) 7 = (ZMod.χ₈ 7 : ℤ) * jacobiSym (3 : ℤ) 7 := by
  rw [jac2_3_7, chi8_7, jacm_3_7]
  decide

private theorem bridgeRed4_3_7 : jacobiSym (4 * (3 : ℤ)) 7 = jacobiSym (3 : ℤ) 7 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

private theorem bridgeRed2_3_7 :
    jacobiSym (2 * (3 : ℤ)) 7 = (ZMod.χ₈ 7 : ℤ) * jacobiSym (3 : ℤ) 7 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

private theorem jac4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = -1 := by norm_num

private theorem jacm_5_3 : jacobiSym (5 : ℤ) 3 = -1 := by norm_num

private theorem jac2_5_3 : jacobiSym (2 * (5 : ℤ)) 3 = 1 := by norm_num

private theorem chi8_3 : (ZMod.χ₈ 3 : ℤ) = -1 := by
  have hat : jacobiSym (2 : ℤ) 3 = (ZMod.χ₈ 3 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 3 = -1 := by norm_num
  rw [← hat]
  exact hjac

private theorem agreeRed4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = jacobiSym (5 : ℤ) 3 := by
  rw [jac4_5_3, jacm_5_3]

private theorem agreeRed2_5_3 :
    jacobiSym (2 * (5 : ℤ)) 3 = (ZMod.χ₈ 3 : ℤ) * jacobiSym (5 : ℤ) 3 := by
  rw [jac2_5_3, chi8_3, jacm_5_3]
  decide

private theorem bridgeRed4_5_3 : jacobiSym (4 * (5 : ℤ)) 3 = jacobiSym (5 : ℤ) 3 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

private theorem bridgeRed2_5_3 :
    jacobiSym (2 * (5 : ℤ)) 3 = (ZMod.χ₈ 3 : ℤ) * jacobiSym (5 : ℤ) 3 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

private theorem jac4_N3_5 : jacobiSym (4 * (-3 : ℤ)) 5 = -1 := by norm_num

private theorem jacm_N3_5 : jacobiSym (-3 : ℤ) 5 = -1 := by norm_num

private theorem jac2_N3_5 : jacobiSym (2 * (-3 : ℤ)) 5 = 1 := by norm_num

private theorem chi8_5 : (ZMod.χ₈ 5 : ℤ) = -1 := by
  have hat : jacobiSym (2 : ℤ) 5 = (ZMod.χ₈ 5 : ℤ) := jacobiSym.at_two (by decide)
  have hjac : jacobiSym (2 : ℤ) 5 = -1 := by norm_num
  rw [← hat]
  exact hjac

private theorem agreeRed4_N3_5 :
    jacobiSym (4 * (-3 : ℤ)) 5 = jacobiSym (-3 : ℤ) 5 := by
  rw [jac4_N3_5, jacm_N3_5]

private theorem agreeRed2_N3_5 :
    jacobiSym (2 * (-3 : ℤ)) 5 = (ZMod.χ₈ 5 : ℤ) * jacobiSym (-3 : ℤ) 5 := by
  rw [jac2_N3_5, chi8_5, jacm_N3_5]
  decide

private theorem bridgeRed4_N3_5 :
    jacobiSym (4 * (-3 : ℤ)) 5 = jacobiSym (-3 : ℤ) 5 :=
  jacobiSym_four_mul_of_odd _ _ (by decide)

private theorem bridgeRed2_N3_5 :
    jacobiSym (2 * (-3 : ℤ)) 5 = (ZMod.χ₈ 5 : ℤ) * jacobiSym (-3 : ℤ) 5 :=
  jacobiSym_two_mul_of_odd _ _ (by decide)

private theorem kronOddBase7_3 : kroneckerSym (7 : ℤ) 3 = 1 := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 3) := ⟨hp⟩
  have hprime : kroneckerSym (7 : ℤ) 3 = kroneckerAtPrime (7 : ℤ) 3 :=
    kroneckerSym_prime (7 : ℤ) 3 hp
  have hat : kroneckerAtPrime (7 : ℤ) 3 = legendreSym 3 (7 : ℤ) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 3 (7 : ℤ) = jacobiSym (7 : ℤ) 3 :=
    jacobiSym.legendreSym.to_jacobiSym 3 (7 : ℤ)
  have hjac : jacobiSym (7 : ℤ) 3 = 1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem kronOddBase7_5 : kroneckerSym (7 : ℤ) 5 = -1 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : 5 ≠ 2 := by decide
  have hfact : Fact (Nat.Prime 5) := ⟨hp⟩
  have hprime : kroneckerSym (7 : ℤ) 5 = kroneckerAtPrime (7 : ℤ) 5 :=
    kroneckerSym_prime (7 : ℤ) 5 hp
  have hat : kroneckerAtPrime (7 : ℤ) 5 = legendreSym 5 (7 : ℤ) := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym 5 (7 : ℤ) = jacobiSym (7 : ℤ) 5 :=
    jacobiSym.legendreSym.to_jacobiSym 5 (7 : ℤ)
  have hjac : jacobiSym (7 : ℤ) 5 = -1 := by norm_num
  rw [hprime, hat, hleg, hjac]

private theorem kronOddComp7_15 : kroneckerSym (7 : ℤ) 15 = -1 := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  have hmul : kroneckerSym (7 : ℤ) (3 * 5) =
      kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 :=
    kroneckerSym_mul (7 : ℤ) (by decide) 3 5
  rw [h15, hmul, kronOddBase7_3, kronOddBase7_5]
  decide

private theorem agreeMul7_3_5 :
    kroneckerSym (7 : ℤ) 15 = kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 := by
  rw [kronOddComp7_15, kronOddBase7_3, kronOddBase7_5]
  decide

private theorem bridgeMul7_3_5 :
    kroneckerSym (7 : ℤ) (3 * 5) =
      kroneckerSym (7 : ℤ) 3 * kroneckerSym (7 : ℤ) 5 :=
  kroneckerSym_mul_of_odd 7 3 5 (by decide) (by decide)

private theorem jacEqNeg1_9 : jacobiSym (-1 : ℤ) 9 = 1 := by norm_num

private theorem bridgeEqNeg1_9 :
    kroneckerSym (-1 : ℤ) 9 = jacobiSym (-1 : ℤ) 9 :=
  kroneckerSym_eq_jacobiSym_of_odd (-1) 9 (by decide)

private theorem agreeOdd7_15 :
    (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (7 : ℤ) 15 := by
  rw [chi15, jacComp7_15, kronOddComp7_15]
  decide

private theorem bridgeOdd7_15 :
    (ZMod.χ₄ 15 : ℤ) * jacobiSym ((15 : ℕ) : ℤ) (7 : ℤ).natAbs =
      kroneckerSym (7 : ℤ) 15 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
    7 15 (by decide) (by decide)

private theorem jacOddNeg1_9 : jacobiSym ((9 : ℕ) : ℤ) (-1 : ℤ).natAbs = 1 := by norm_num

private theorem bridgeOddNeg1_9 :
    (ZMod.χ₄ 9 : ℤ) * jacobiSym ((9 : ℕ) : ℤ) (-1 : ℤ).natAbs =
      kroneckerSym (-1 : ℤ) 9 :=
  chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
    (-1) 9 (by decide) (by decide)

private theorem scope_mod3 : (3 : ℤ) % 4 = 3 := by decide

private theorem scope_modNeg5 : (-5 : ℤ) % 4 = 3 := by decide

private theorem scope_mod7 : (7 : ℤ) % 4 = 3 := by decide

private theorem scope_modNeg1 : (-1 : ℤ) % 4 = 3 := by decide

private theorem scope_mod5 : (5 : ℤ) % 4 = 1 := by decide

private theorem scope_odd7 : Odd (7 : ℕ) := by decide

private theorem scope_odd9 : Odd (9 : ℕ) := by decide

private theorem scope_odd15 : Odd (15 : ℕ) := by decide
