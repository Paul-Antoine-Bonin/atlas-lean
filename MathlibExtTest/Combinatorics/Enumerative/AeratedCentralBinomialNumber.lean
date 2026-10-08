/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AeratedCentralBinomialNumber

namespace MetaMathlibExt

example : List.ofFn (fun i : Fin 7 => aeratedCentralBinomialNumber i) =
    [1, 0, 2, 0, 6, 0, 20] := by decide

end MetaMathlibExt
