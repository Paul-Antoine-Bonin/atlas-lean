module

import MathlibExt.NumberTheory.NormalNumber

open MetaMathlibExt.NormalNumber

example (b n : ℕ) (x : ℝ) : digitSeq b x n = ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b :=
  rfl

#check IsNormalInBase.isSimplyNormalInBase
#check IsAbsolutelyNormal

#print axioms digitSeq
#print axioms IsSimplyNormalInBase
#print axioms IsNormalInBase
#print axioms IsAbsolutelyNormal
