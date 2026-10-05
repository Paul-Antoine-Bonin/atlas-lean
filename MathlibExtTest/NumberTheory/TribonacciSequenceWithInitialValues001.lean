module

public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

@[expose] public section

namespace MetaMathlibExt

example : tribonacci 0 = 0 := rfl
example : tribonacci 1 = 0 := rfl
example : tribonacci 2 = 1 := rfl
example : tribonacci 3 = 1 := rfl
example : tribonacci 4 = 2 := rfl
example : tribonacci 5 = 4 := rfl

example (n : ℕ) :
    tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl

end MetaMathlibExt
