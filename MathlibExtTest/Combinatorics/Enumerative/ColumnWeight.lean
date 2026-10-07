/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColumnWeight

namespace MetaMathlibExt

example : columnWeight 3 (fun multiplicity => multiplicity + 1)
    ([0, 1, 0] : List (Fin 3)) = 6 := by decide

end MetaMathlibExt
