/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import Batteries.Util.ProofWanted

@[expose] public section

open Cslib.CookLevin

namespace MetaMathlibExt

/-- Cook–Levin theorem: SAT is NP-complete, i.e. SAT is in NP and every
NP decision problem reduces in polynomial time to SAT. Both membership and
hardness are stated through the canonical `ComplexityTheory` API, so this is
completeness for the same NP class used by the P-vs-NP statements.

Sources: Stephen A. Cook, "The Complexity of Theorem-Proving Procedures,"
STOC 1971, 151–158, <https://doi.org/10.1145/800157.805047>; Leonid A. Levin,
"Universal Sequential Search Problems," *Problems of Information
Transmission* 9.3 (1973), 265–266; and
<https://en.wikipedia.org/wiki/Cook%E2%80%93Levin_theorem>. -/
theorem_wanted cook_levin_SAT_np_complete :
    satDec ∈ ComplexityTheory.NP ∧
      ∀ L : ComplexityTheory.DecisionProblem,
        L ∈ ComplexityTheory.NP → PolyManyOneRed L satDec

end MetaMathlibExt
