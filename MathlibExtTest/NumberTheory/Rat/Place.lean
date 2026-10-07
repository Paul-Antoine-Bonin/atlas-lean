/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.Place

namespace Rat.Place

example : CompletedField .infinite = ℝ := completedField_infinite

example : CompleteSpace (CompletedField .infinite) := inferInstance

example (q : ℚ) : ‖embedding .infinite q‖ = absoluteValue .infinite q :=
  embedding_norm_eq_absoluteValue .infinite q

example (prime : Nat.Primes) :
    letI : Fact prime.1.Prime := ⟨prime.2⟩
    CompletedField (.finite prime) = Padic prime.1 :=
  completedField_finite prime

example (prime : Nat.Primes) (q : ℚ) :
    ‖embedding (.finite prime) q‖ = absoluteValue (.finite prime) q :=
  embedding_norm_eq_absoluteValue (.finite prime) q

example (v : Place) : DenseRange v.embedding := denseRange_embedding v

example (v : Place) : Isometry v.withAbsEmbedding := withAbsEmbedding_isometry v

example (v : Place) : DenseRange v.withAbsEmbedding := denseRange_withAbsEmbedding v

example (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    ∃! v : Place, f ≈ v.absoluteValue :=
  exists_unique_place_equiv f hf

end Rat.Place
