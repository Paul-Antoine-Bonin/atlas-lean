module

public import MathlibExt.NumberTheory.CountingOppermannPrimes

namespace MetaMathlibExt

example : oppermannLowerPrimeCount 2 = 2 := by decide
example : oppermannUpperPrimeCount 2 = 1 := by decide

#print axioms oppermannLowerPrimeCount
#print axioms oppermannUpperPrimeCount
#print axioms oppermannAsymptotic

end MetaMathlibExt
