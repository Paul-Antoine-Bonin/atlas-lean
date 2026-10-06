module

public import MathlibExt.Combinatorics.Enumerative.ColumnWeight

namespace MetaMathlibExt

example : columnWeight 3 (fun multiplicity => multiplicity + 1)
    ([0, 1, 0] : List (Fin 3)) = 6 := by decide

end MetaMathlibExt
