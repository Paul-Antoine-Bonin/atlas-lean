/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Disjoint

@[expose] public section

/-!
# Erdős Problem #869

If `A₁` and `A₂` are disjoint additive bases of order `2`, must their
union contain a minimal additive basis of order `2`?
-/

namespace MathlibExt.NumberTheory.ErdosProblem869Wanted

/-- Sumset `A + A` of a set of naturals, as used in the basis condition of
EP-869 [Erdős Problems]. -/
def addSumset (A : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ A, a + b = n }

/-- `A` is an additive basis of order `2` in the sense of EP-869 [Erdős Problems]:
`A + A` contains all sufficiently large integers. -/
def IsAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- `A` is a minimal additive basis of order `2` in the sense of EP-869
[Erdős Problems]: it is a basis, and deleting any element leaves infinitely
many integers outside the sumset. -/
def IsMinimalAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  IsAdditiveBasisOrder2 A ∧ ∀ a ∈ A, ((addSumset (A \ {a}))ᶜ).Infinite

/-- Erdős Problem #869 [Erdős Problems]: if `A₁` and `A₂` are disjoint additive
bases of order `2`, must their union contain a minimal additive basis of order `2`? -/
def Statement : Prop :=
  ∀ A1 A2 : Set ℕ, Disjoint A1 A2 → IsAdditiveBasisOrder2 A1 →
    IsAdditiveBasisOrder2 A2 →
    ∃ B : Set ℕ, B ⊆ A1 ∪ A2 ∧ IsMinimalAdditiveBasisOrder2 B

/--
Resolved false: Larsen constructed disjoint additive bases of order two whose union contains no
minimal additive basis of order two. Source: Daniel Larsen, Three questions of Erdős–Nathanson
on asymptotic bases of order 2, arXiv:2603.03472 (2026), https://arxiv.org/abs/2603.03472; Lean
proof of the negative answer to Erdős Problem 869, pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos869.lean#L3490.
Moved from `OpenConjectures/NumberTheory/ErdosProblem869`.
-/
public theorem_wanted Statement_refuted : ¬ Statement

end MathlibExt.NumberTheory.ErdosProblem869Wanted
