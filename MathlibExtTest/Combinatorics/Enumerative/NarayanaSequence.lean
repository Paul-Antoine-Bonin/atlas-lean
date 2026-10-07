/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import Mathlib.Data.List.Range

namespace MetaMathlibExt

example : (List.range 7).map narayanaCowsSequence = [0, 1, 1, 1, 2, 3, 4] := by
  decide

example (n : ℕ) :
    narayanaCowsSequence (n + 3) =
      narayanaCowsSequence (n + 2) + narayanaCowsSequence n :=
  rfl

end MetaMathlibExt
