/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence

namespace MetaMathlibExt.GeneralizedThueMorse

example : classicalBlock 2 =
    [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  decide

example : List.ofFn
    (fun i : Fin 8 => infLetter 2 2 (by decide) (by decide) classicalKappa i) =
      [(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1] := by
  decide

end MetaMathlibExt.GeneralizedThueMorse
