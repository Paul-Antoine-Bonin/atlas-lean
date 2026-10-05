module

public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber

namespace MetaMathlibExt

example : pellLucas 0 = 2 := rfl
example : pellLucas 1 = 2 := rfl
example : pellLucas 2 = 6 := rfl
example : pellLucas 3 = 14 := rfl
example : pellLucas 4 = 34 := rfl

end MetaMathlibExt
