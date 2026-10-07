/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-accessibility of primes

`OPG-1797` (Open Problem Garden, node 1797): is the set of prime
numbers 2-accessible?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted

/-- Monochromatic finite sequence: all terms receive the same color.

Source `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
formalizes "monochromatic sequence" from the definition of `r`-accessible. -/
def IsMonochromatic {r k : ℕ} (c : ℕ → Fin r) (x : Fin k → ℕ) : Prop :=
  ∀ i j, c (x i) = c (x j)

/-- `S`-diffsequence: consecutive terms differ by an element of `S`.

Source `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
formalizes "`S`-diffsequence", i.e. `x_{i+1} - x_i ∈ S`,
stated additively as `x (i+1) = x i + d` with `d ∈ S`. -/
def IsSDiffSequence (S : Set ℕ) {k : ℕ} (x : Fin k → ℕ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < k), ∃ d ∈ S, x ⟨i + 1, h⟩ = x ⟨i, by omega⟩ + d

/-- `r`-accessibility of a set `S ⊆ ℕ`.

Source `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
`S` is `r`-accessible if for every `r`-coloring of `ℕ` and every
`k ∈ ℕ \ {1}` there is a monochromatic `S`-diffsequence of length `k`. -/
def IsRAccessible (r : ℕ) (S : Set ℕ) : Prop :=
  ∀ (c : ℕ → Fin r) (k : ℕ), k ≠ 1 → ∃ x : Fin k → ℕ,
    IsMonochromatic c x ∧ IsSDiffSequence S x

/-- Open question `OPG-1797`: is the set of primes 2-accessible?

Source `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
"Is the set of prime numbers 2-accessible?" -/
def conjecture : Prop :=
  IsRAccessible 2 { n | Nat.Prime n }

/--
Resolved true: Quester (arXiv:2606.00410, May 2026, Theorem 1 with N = 2) proves the primes are
2-accessible: every 2-colouring of N has arbitrarily long monochromatic prime-diffsequences,
using the Frantzikinakis-Host-Kra shifted-prime recurrence theorem. Source: Oscar Quester, The
Primes are 2-Accessible, arXiv preprint (2026), arXiv:2606.00410,
https://arxiv.org/abs/2606.00410; Nikos Frantzikinakis, Bernard Host, Bryna Kra, The polynomial
multidimensional Szemeredi theorem along shifted primes, Israel J. Math. 194 (2013), 331-348,
arXiv:1009.1484, https://arxiv.org/abs/1009.1484. Moved from
`OpenConjectures/Combinatorics/PrimeTwoAccessibility`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted
