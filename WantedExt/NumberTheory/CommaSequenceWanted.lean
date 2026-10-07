/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CommaSequence

namespace MetaMathlibExt

@[expose] public section

/-- Comma sequences with arbitrary positive initial values terminate in every
base from 3 through 633 inclusive.

This is statement `commaSequence_terminates_of_base_le_633` from lines 134–137 of
Dougherty, *Comma Sequences*, JIS 28, with the sequence semantics defined in
`MathlibExt.NumberTheory.CommaSequence`. -/
public theorem_wanted commaSequence_terminates_of_base_le_633
    (b v : ℕ) (hb1 : 3 ≤ b) (hb2 : b ≤ 633) (hv : 0 < v) :
    IsCommaTerminating b v

end

end MetaMathlibExt
