/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ComplementarySequenceDeterminedBySubsequenceSumEquation

namespace MetaMathlibExt

example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) (n : ℕ) : 0 < a n := h.1 n
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) (n : ℕ) : 0 < b n := h.2.1 n
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) : StrictMono a := h.2.2.1
example (a b : ℕ → ℕ) (h : IsComplementaryPair a b) : StrictMono b := h.2.2.2.1

#print axioms IsComplementaryPair
#print axioms SatisfiesParametrizedSumEquation

end MetaMathlibExt
