module

public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction

namespace MetaMathlibExt

example : takagiBit 5 0 = 1 := by decide
example : takagiBit 5 1 = 0 := by decide
example : takagiBit 5 2 = 1 := by decide
example : takagiBit 5 (-1) = 0 := by decide
example : takagiEll 1 0 2 = 1 := by decide

end MetaMathlibExt
