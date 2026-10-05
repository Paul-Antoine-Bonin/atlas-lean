module

public import MathlibExt.Combinatorics.Enumerative.OctanacciNumber

namespace MetaMathlibExt

example : octanacciNumber 0 = 1 := by decide
example : octanacciNumber 8 = 128 := by decide
example : octanacciNumber 9 = 255 := by decide

end MetaMathlibExt
