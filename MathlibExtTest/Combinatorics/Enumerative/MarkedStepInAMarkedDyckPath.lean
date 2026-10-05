module

public import MathlibExt.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath

namespace MetaMathlibExt

open MarkedDyckStep

example : markedDyckCountE [E, Nstar, E, N] = 2 := by rfl
example : markedDyckCountN [E, Nstar, E, N] = 1 := by rfl
example : markedDyckCountNstar [E, Nstar, E, N] = 1 := by rfl

end MetaMathlibExt
