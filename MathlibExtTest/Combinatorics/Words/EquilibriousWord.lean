/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.EquilibriousWord

open MetaMathlibExt

example : IsEquilibriousWord [] := by decide

example : ¬ IsEquilibriousWord [(0 : Fin 2)] := by decide

example : IsEquilibriousWord [(0 : Fin 2), 1] := by decide

example : ¬ IsEquilibriousWord [(0 : Fin 2), 0, 1] := by decide

example : IsEquilibriousWord ([(0 : Fin 2), 1].reverse) := by decide

example : IsEquilibriousWord ([(0 : Fin 2), 1].reverse) ↔
    IsEquilibriousWord [(0 : Fin 2), 1] :=
  isEquilibriousWord_reverse
