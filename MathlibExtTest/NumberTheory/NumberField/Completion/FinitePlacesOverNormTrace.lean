/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverNormTrace

@[expose] public section

/-!
# Tests for the norm/trace completion decomposition

These tests exercise the number-field specialization of ATLAS `NumberTheoryI`
target N237, Corollary 11.24 (at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, `targets.yaml` lines 1685--1693,
primary Lean source `LocalGlobal.lean` lines 1111--1435): generic use of the
norm identity, generic use of the trace identity, and reconstruction of the
full two-clause conjunction.
-/

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open scoped NumberField.LiesOver
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.placesOver L)]

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- Exact generic use of the norm identity.
example (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
      ∏ w : v.placesOver L, Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.val.adicCompletion L) α) :=
  algebraMap_norm_eq_prod_adicCompletion (K := K) (L := L) v α

-- Exact generic use of the trace identity.
example (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
      ∑ w : v.placesOver L, Algebra.trace (v.adicCompletion K)
        (w.val.adicCompletion L)
        (algebraMap L (w.val.adicCompletion L) α) :=
  algebraMap_trace_eq_sum_adicCompletion (K := K) (L := L) v α

-- Reconstruction of the full two-clause Corollary 11.24 conjunction.
example (α : L) :
    (algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
      ∏ w : v.placesOver L, Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.val.adicCompletion L) α))
    ∧
    (algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
      ∑ w : v.placesOver L, Algebra.trace (v.adicCompletion K)
        (w.val.adicCompletion L)
        (algebraMap L (w.val.adicCompletion L) α)) :=
  ⟨algebraMap_norm_eq_prod_adicCompletion (K := K) (L := L) v α,
    algebraMap_trace_eq_sum_adicCompletion (K := K) (L := L) v α⟩
