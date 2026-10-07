/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace MetaMathlibExt

/-! # Girth-eight monomial graph classification -/

/--
Classification of girth-eight monomial graphs over odd finite fields when either the
characteristic is at least five and the extension degree has no prime factor above three, or the
field cardinality is at most `10 ^ 10`.
Source: V. Dmytrenko, F. Lazebnik, and J. Williford, "On monomial graphs of girth eight",
Finite Fields Appl. 13 (2007), 828–842, Theorem 3.
-/
public theorem_wanted monomialGraph_girth_eight_classification
    (p e q : ℕ) (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [CharP 𝔽 p]
    (hp : p.Prime) (hp_odd : Odd p) (hq : q = p ^ e)
    (hcard : Fintype.card 𝔽 = q)
    (hcase : (5 ≤ p ∧ ∃ a b : ℕ, e = 2 ^ a * 3 ^ b) ∨ (3 ≤ q ∧ q ≤ 10 ^ 10)) :
    ∀ m₂ n₂ m₃ n₃ : ℕ,
      let G : SimpleGraph (Sum (𝔽 × 𝔽 × 𝔽) (𝔽 × 𝔽 × 𝔽)) :=
        SimpleGraph.fromRel fun u v ↦
          match u, v with
          | Sum.inl (x₁, x₂, x₃), Sum.inr (y₁, y₂, y₃) =>
              x₂ + y₂ = x₁ ^ m₂ * y₁ ^ n₂ ∧
                x₃ + y₃ = x₁ ^ m₃ * y₁ ^ n₃
          | _, _ => False
      let Γ₃ : SimpleGraph (Sum (𝔽 × 𝔽 × 𝔽) (𝔽 × 𝔽 × 𝔽)) :=
        SimpleGraph.fromRel fun u v ↦
          match u, v with
          | Sum.inl (x₁, x₂, x₃), Sum.inr (y₁, y₂, y₃) =>
              x₂ + y₂ = x₁ * y₁ ∧ x₃ + y₃ = x₁ * y₁ ^ 2
          | _, _ => False
      8 ≤ G.girth → Nonempty (G ≃g Γ₃) ∧ G.girth = 8

end MetaMathlibExt
