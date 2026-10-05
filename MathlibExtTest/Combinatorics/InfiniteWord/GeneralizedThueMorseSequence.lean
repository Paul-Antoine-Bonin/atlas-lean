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
