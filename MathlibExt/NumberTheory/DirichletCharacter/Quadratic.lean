/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

/-! Quadratic Dirichlet character support definitions.

Source: Joshua Males, Andreas Mono, Larry Rolen, and Ian Wagner,
*Central L-values of newforms and local polynomials*,
`arXiv:2306.15519v5`, final author version linked to
Journal of Number Theory 291 (2027), 101-137, DOI `10.1016/j.jnt.2026.04.009`.
Frozen TeX: `source/CentralLvaluesPartI+II_arXiv05.tex`,
SHA-256 `5575769386f5cc658f50eed8c7300131a327588b5e5f9244dc382da460fddc99`.
Frozen metadata: `source/arxiv_2306_15519v5_metadata.json`,
SHA-256 `cb10efb2bcb9bab9d029caada155edcb289c4ade62d2f632558f656efc76d3b1`.
Source location: subsection "L-functions and L-values", physical line 455,
before the active `end{document}` at line 2067.
Full physical line SHA-256:
`d3abff40520b73b3b70787606206c0f1c22b2b30bae94a2fcb05b542a77bc8ea`.
Exact quoted substring SHA-256:
`23044c9cbc274e07312045c84af50eb4b675424cc6daa71f3063a611d071af1e`.
Exact source sentence: "One may also consider L-functions associated to
a Dirichlet character chi_D = (D / dot), namely ...".
Stable ID: `candidate:a:ef6cab2596e5dbf9`. -/
namespace MetaMathlibExt

/-- Fundamental discriminant predicate from the source contract:
either `D` is squarefree and congruent to `1` modulo `4`,
or `D = 4 * m` with `m` squarefree and congruent to `2` or `3` modulo `4`.
Includes `D = 1`, excludes `D = 0`. -/
public def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (Squarefree D ∧ D % 4 = 1) ∨
    ∃ m : ℤ, D = 4 * m ∧ Squarefree m ∧ (m % 4 = 2 ∨ m % 4 = 3)

/-- Kronecker symbol at the prime two via the standard mod-eight rule. -/
public def kroneckerAtTwo (D : ℤ) : ℤ :=
  if D % 2 = 0 then 0
  else if D % 8 = 1 ∨ D % 8 = 7 then 1
  else -1

/-- Kronecker symbol at a prime: mod-eight rule at two, Legendre elsewhere. -/
public def kroneckerAtPrime (D : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then kroneckerAtTwo D
  else if h : p.Prime then @legendreSym p (Fact.mk h) D
  else 0

/-- Positive-denominator Kronecker symbol, with multiplicity preserved. -/
public def kroneckerSym (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then if D.natAbs = 1 then 1 else 0
  else (n.primeFactorsList.map (kroneckerAtPrime D)).prod

public theorem kroneckerSym_zero (D : ℤ) :
    kroneckerSym D 0 = if D.natAbs = 1 then 1 else 0 := by
  simp [kroneckerSym]

public theorem kroneckerSym_one (D : ℤ) : kroneckerSym D 1 = 1 := by
  simp [kroneckerSym]

public theorem kroneckerAtPrime_two (D : ℤ) :
    kroneckerAtPrime D 2 = kroneckerAtTwo D := by
  simp [kroneckerAtPrime]

public theorem kroneckerSym_two (D : ℤ) :
    kroneckerSym D 2 = kroneckerAtTwo D := by
  have hprime : Nat.Prime 2 := Nat.prime_two
  have hlist : Nat.primeFactorsList 2 = [2] :=
    Nat.primeFactorsList_prime hprime
  rw [kroneckerSym, ite_eq_right (by decide), hlist]
  simp [kroneckerAtPrime]

/-- Kronecker symbol at a prime lower argument reduces to the prime dispatcher. -/
public theorem kroneckerSym_prime (D : ℤ) (p : ℕ) (hp : p.Prime) :
    kroneckerSym D p = kroneckerAtPrime D p := by
  have hne : p ≠ 0 := hp.ne_zero
  have hlist : p.primeFactorsList = [p] := Nat.primeFactorsList_prime hp
  rw [kroneckerSym, ite_eq_right hne, hlist]
  simp

end MetaMathlibExt

end
