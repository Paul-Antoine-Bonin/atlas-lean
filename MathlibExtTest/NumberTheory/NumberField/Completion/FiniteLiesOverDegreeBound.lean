/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound

/-!
# Tests for the local degree bound under finite-place completion

Generic checks consuming `finrank_adicCompletion_le`: one direct API
application and one downstream `calc`/transitivity use. These tests
exercise the public inequality only and do not duplicate its proof.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
      Module.finrank K L :=
  finrank_adicCompletion_le v w

example {n : ℕ} (h : Module.finrank K L ≤ n) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤ n :=
  calc Module.finrank (v.adicCompletion K) (w.adicCompletion L)
      ≤ Module.finrank K L := finrank_adicCompletion_le v w
    _ ≤ n := h

end IsDedekindDomain.HeightOneSpectrum
