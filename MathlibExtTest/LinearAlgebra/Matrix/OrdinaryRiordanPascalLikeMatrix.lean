module

public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

namespace MetaMathlibExt

example : ordinaryRiordanPascalLikeMatrix 0 0 0 = 1 := by decide
example : ordinaryRiordanPascalLikeMatrix 2 1 1 = 3 := by decide
example : ordinaryRiordanPascalLikeMatrix 3 1 1 = 5 := by decide

end MetaMathlibExt
