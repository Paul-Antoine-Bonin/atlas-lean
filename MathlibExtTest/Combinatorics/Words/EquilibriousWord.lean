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
